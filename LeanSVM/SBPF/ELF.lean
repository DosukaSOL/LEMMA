/-
  LeanSVM.SBPF.ELF
  Direct native Lean 4 ELF64 shared-object (.so) linker and serializer for Solana sBPF.
  Produces minimal, zero-bloat `.so` binaries accepted directly by Solana Agave & LiteSVM:
  - SBPF V0: contiguous RO sections (`.text`, optional `.rodata`) for zero-copy `Section::Borrowed`;
    `.dynamic`/`.dynsym`/`.dynstr`/`.rel.dyn` emitted ONLY when external syscalls are used.
  - SBPF V3: strict 4-PHDR ELF (`EM_SBPF`, `e_flags=3`, static syscalls, 0 relocations).
-/
import LeanSVM.SBPF.ISA

namespace LeanSVM.SBPF

private def alignUp (n align : Nat) : Nat :=
  if align <= 1 then n else ((n + align - 1) / align) * align

private def padTo (buf : ByteArray) (targetSize : Nat) : ByteArray := Id.run do
  let mut b := buf
  while b.size < targetSize do
    b := b.push 0
  return b

/-- Build an ELF string table and return `(bytes, offsetOf)` helper. -/
private structure StrTab where
  bytes   : ByteArray
  offsets : List (String × UInt32)

private def buildStrTab (names : List String) : StrTab := Id.run do
  let mut buf := ByteArray.empty.push 0 -- index 0 is empty string ""
  let mut offs : List (String × UInt32) := [("", 0)]
  for name in names do
    if offs.all (fun p => p.1 != name) then
      let off := buf.size.toUInt32
      buf := buf ++ name.toUTF8
      buf := buf.push 0
      offs := (name, off) :: offs
  return { bytes := buf, offsets := offs }

private def StrTab.off (st : StrTab) (name : String) : UInt32 :=
  match st.offsets.find? (fun p => p.1 == name) with
  | some (_, o) => o
  | none => 0

/-- Write a 64-byte `Elf64_Ehdr`. -/
private def pushEhdr (buf : ByteArray)
    (eMachine : UInt16) (eEntry ePhoff eShoff : UInt64)
    (eFlags : UInt32) (ePhnum eShnum eShstrndx : UInt16) : ByteArray :=
  let b := buf
    -- e_ident[16]
    |>.push 0x7f |>.push 0x45 |>.push 0x4c |>.push 0x46 -- \x7fELF
    |>.push 2    -- ELFCLASS64
    |>.push 1    -- ELFDATA2LSB
    |>.push 1    -- EV_CURRENT
    |>.push 0    -- ELFOSABI_NONE
    |>.push 0 |>.push 0 |>.push 0 |>.push 0 |>.push 0 |>.push 0 |>.push 0 |>.push 0
  let b := pushU16LE b 3          -- e_type = ET_DYN
  let b := pushU16LE b eMachine   -- e_machine = EM_BPF (247) or EM_SBPF (263)
  let b := pushU32LE b 1          -- e_version = EV_CURRENT
  let b := pushU64LE b eEntry     -- e_entry
  let b := pushU64LE b ePhoff     -- e_phoff
  let b := pushU64LE b eShoff     -- e_shoff
  let b := pushU32LE b eFlags     -- e_flags (0 = V0, 3 = V3)
  let b := pushU16LE b 64         -- e_ehsize
  let b := pushU16LE b 56         -- e_phentsize
  let b := pushU16LE b ePhnum     -- e_phnum
  let b := pushU16LE b 64         -- e_shentsize
  let b := pushU16LE b eShnum     -- e_shnum
  pushU16LE b eShstrndx           -- e_shstrndx

/-- Write a 56-byte `Elf64_Phdr`. -/
private def pushPhdr (buf : ByteArray)
    (pType pFlags : UInt32) (pOffset pVaddr pPaddr pFilesz pMemsz pAlign : UInt64) : ByteArray :=
  let b := pushU32LE buf pType
  let b := pushU32LE b pFlags
  let b := pushU64LE b pOffset
  let b := pushU64LE b pVaddr
  let b := pushU64LE b pPaddr
  let b := pushU64LE b pFilesz
  let b := pushU64LE b pMemsz
  pushU64LE b pAlign

/-- Write a 64-byte `Elf64_Shdr`. -/
private def pushShdr (buf : ByteArray)
    (shName shType : UInt32) (shFlags shAddr shOffset shSize : UInt64)
    (shLink shInfo : UInt32) (shAddralign shEntsize : UInt64) : ByteArray :=
  let b := pushU32LE buf shName
  let b := pushU32LE b shType
  let b := pushU64LE b shFlags
  let b := pushU64LE b shAddr
  let b := pushU64LE b shOffset
  let b := pushU64LE b shSize
  let b := pushU32LE b shLink
  let b := pushU32LE b shInfo
  let b := pushU64LE b shAddralign
  pushU64LE b shEntsize

/-- Write a 24-byte `Elf64_Sym`. -/
private def pushSym (buf : ByteArray)
    (stName : UInt32) (stInfo stOther : UInt8) (stShndx : UInt16)
    (stValue stSize : UInt64) : ByteArray :=
  let b := pushU32LE buf stName |>.push stInfo |>.push stOther
  let b := pushU16LE b stShndx
  let b := pushU64LE b stValue
  pushU64LE b stSize

/-- Write a 16-byte `Elf64_Rel`. -/
private def pushRel (buf : ByteArray) (rOffset rInfo : UInt64) : ByteArray :=
  pushU64LE (pushU64LE buf rOffset) rInfo

/-- Write a 16-byte `Elf64_Dyn`. -/
private def pushDyn (buf : ByteArray) (dTag dVal : UInt64) : ByteArray :=
  pushU64LE (pushU64LE buf dTag) dVal

/-- Deduplicate syscall symbol names preserving deterministic first-seen order. -/
private def uniqueSyscalls (relocs : Array SyscallReloc) : Array String := Id.run do
  let mut seen : Array String := #[]
  for r in relocs do
    if !seen.contains r.symName then
      seen := seen.push r.symName
  return seen

/-- Emit a minimal, valid Solana SBPF V0 ELF64 `.so` shared object directly from symbolic
    sBPF instructions and `.rodata` bytes.

    Layout (all offsets 8-byte aligned, `.text` and `.rodata` contiguous with `sh_addr == sh_offset`):
    - `[0..64)`       ELF64 Header (`EM_BPF = 247`, `e_flags = 0`)
    - `[64..64+56*P)` Program Headers (`PT_LOAD` for RO, optional `PT_DYNAMIC` if syscalls exist)
    - `.text`         Executable sBPF bytecode (entry point = `textOff`)
    - `.rodata`       Read-only string/constant data (omitted if empty)
    - (if syscalls):  `.dynsym`, `.dynstr`, `.rel.dyn`, `.dynamic`
    - `.shstrtab`     Section name string table
    - Section Header Table
-/
def emitElfV0 (insns : Array Insn) (rodata : ByteArray) : Except String (ByteArray × AssembledText) := do
  -- First assemble with dummy rodataBaseVaddr to inspect text size & syscall relocs
  let probe ← assemble insns .v0 0x100000000
  let hasRodata := rodata.size > 0
  let syscalls := uniqueSyscalls probe.syscallRelocs
  let hasDynamic := syscalls.size > 0

  let phnum : Nat := if hasDynamic then 2 else 1
  let textOff : Nat := alignUp (64 + 56 * phnum) 8
  let textSize : Nat := probe.bytes.size
  let rodataOff : Nat := alignUp (textOff + textSize) 8
  let rodataSize : Nat := rodata.size
  let roEnd : Nat := if hasRodata then rodataOff + rodataSize else textOff + textSize

  -- Re-assemble with exact `.rodata` VM virtual address (`MM_RODATA_START + rodataOff`)!
  let rodataVaddr : UInt64 := 0x100000000 + rodataOff.toUInt64
  let asm ← assemble insns .v0 rodataVaddr

  -- Build dynamic tables if syscalls are present
  let dynStrNames : List String := "entrypoint" :: syscalls.toList
  let dynstr := buildStrTab dynStrNames
  -- .dynsym: [0] NULL, [1] entrypoint (STT_FUNC, STB_GLOBAL, shndx=1), [2..] undefined syscalls
  let mut dynsymBytes := ByteArray.empty
  if hasDynamic then
    dynsymBytes := pushSym dynsymBytes 0 0 0 0 0 0 -- STN_UNDEF
    -- entrypoint symbol: STB_GLOBAL (1<<4) | STT_FUNC (2) = 0x12
    dynsymBytes := pushSym dynsymBytes (dynstr.off "entrypoint") 0x12 0 1 textOff.toUInt64 textSize.toUInt64
    for sc in syscalls do
      -- undefined external syscall: STB_GLOBAL (1<<4) | STT_NOTYPE (0) = 0x10, SHN_UNDEF = 0
      dynsymBytes := pushSym dynsymBytes (dynstr.off sc) 0x10 0 0 0 0

  let mut relDynBytes := ByteArray.empty
  if hasDynamic then
    for r in asm.syscallRelocs do
      let symIdx : UInt64 :=
        match syscalls.findIdx? (· == r.symName) with
        | some idx => (idx + 2).toUInt64 -- +2 skips STN_UNDEF(0) and entrypoint(1)
        | none => 0
      let rOffset : UInt64 := textOff.toUInt64 + r.textByteOffset
      -- R_BPF_64_32 = 10
      let rInfo : UInt64 := (symIdx <<< 32) ||| 10
      relDynBytes := pushRel relDynBytes rOffset rInfo

  -- Compute file offsets for optional dynamic sections
  let dynsymOff := alignUp roEnd 8
  let dynstrOff := alignUp (dynsymOff + dynsymBytes.size) 8
  let relDynOff := alignUp (dynstrOff + dynstr.bytes.size) 8
  let dynamicOff := alignUp (relDynOff + relDynBytes.size) 8

  let mut dynamicBytes := ByteArray.empty
  if hasDynamic then
    -- DT_REL (17), DT_RELSZ (18), DT_RELENT (19), DT_SYMTAB (6), DT_SYMENT (11), DT_STRTAB (5), DT_STRSZ (10), DT_FLAGS (30), DT_NULL (0)
    dynamicBytes := pushDyn dynamicBytes 17 relDynOff.toUInt64
    dynamicBytes := pushDyn dynamicBytes 18 relDynBytes.size.toUInt64
    dynamicBytes := pushDyn dynamicBytes 19 16
    dynamicBytes := pushDyn dynamicBytes 6  dynsymOff.toUInt64
    dynamicBytes := pushDyn dynamicBytes 11 24
    dynamicBytes := pushDyn dynamicBytes 5  dynstrOff.toUInt64
    dynamicBytes := pushDyn dynamicBytes 10 dynstr.bytes.size.toUInt64
    dynamicBytes := pushDyn dynamicBytes 0  0

  -- Build `.shstrtab`
  let mut shNames : List String := [".text", ".shstrtab"]
  if hasRodata then shNames := ".rodata" :: shNames
  if hasDynamic then shNames := [".dynsym", ".dynstr", ".rel.dyn", ".dynamic"] ++ shNames
  let shstrtab := buildStrTab shNames

  let shstrtabOff :=
    if hasDynamic then alignUp (dynamicOff + dynamicBytes.size) 8
    else alignUp roEnd 8
  let shoff := alignUp (shstrtabOff + shstrtab.bytes.size) 8

  -- Compute section indices:
  -- 0: NULL
  -- 1: .text
  -- (optional) .rodata
  -- (optional) .dynsym, .dynstr, .rel.dyn, .dynamic
  -- last: .shstrtab
  let mut nextShIdx : Nat := 2
  let mut rodataShIdx : Nat := 0
  let mut dynsymShIdx : Nat := 0
  let mut dynstrShIdx : Nat := 0
  if hasRodata then
    rodataShIdx := nextShIdx
    nextShIdx := nextShIdx + 1
  if hasDynamic then
    dynsymShIdx := nextShIdx
    dynstrShIdx := nextShIdx + 1
    nextShIdx := nextShIdx + 4
  let shstrtabShIdx := nextShIdx
  let shnum := nextShIdx + 1

  -- Serialize ELF64 binary!
  let mut out := ByteArray.emptyWithCapacity (shoff + shnum * 64)
  out := pushEhdr out 247 textOff.toUInt64 64 shoff.toUInt64 0 phnum.toUInt16 shnum.toUInt16 shstrtabShIdx.toUInt16

  -- Program Header 0: PT_LOAD (1), PF_R|PF_X (5) covering `.text`, `.rodata`, and dynamic tables
  let loadEnd := if hasDynamic then dynamicOff + dynamicBytes.size else roEnd
  let loadSize := loadEnd - textOff
  out := pushPhdr out 1 5 textOff.toUInt64 textOff.toUInt64 textOff.toUInt64 loadSize.toUInt64 loadSize.toUInt64 8

  -- Program Header 1 (optional): PT_DYNAMIC (2), PF_R|PF_W (6)
  if hasDynamic then
    out := pushPhdr out 2 6 dynamicOff.toUInt64 dynamicOff.toUInt64 dynamicOff.toUInt64
      dynamicBytes.size.toUInt64 dynamicBytes.size.toUInt64 8

  -- `.text`
  out := padTo out textOff
  out := out ++ asm.bytes

  -- `.rodata`
  if hasRodata then
    out := padTo out rodataOff
    out := out ++ rodata

  -- Dynamic sections
  if hasDynamic then
    out := padTo out dynsymOff
    out := out ++ dynsymBytes
    out := padTo out dynstrOff
    out := out ++ dynstr.bytes
    out := padTo out relDynOff
    out := out ++ relDynBytes
    out := padTo out dynamicOff
    out := out ++ dynamicBytes

  -- `.shstrtab`
  out := padTo out shstrtabOff
  out := out ++ shstrtab.bytes

  -- Section Header Table
  out := padTo out shoff
  -- [0] NULL
  out := pushShdr out 0 0 0 0 0 0 0 0 0 0
  -- [1] .text: SHT_PROGBITS (1), SHF_ALLOC|SHF_EXECINSTR (6)
  out := pushShdr out (shstrtab.off ".text") 1 6 textOff.toUInt64 textOff.toUInt64 textSize.toUInt64 0 0 8 0
  -- .rodata: SHT_PROGBITS (1), SHF_ALLOC (2)
  if hasRodata then
    let _ := rodataShIdx
    out := pushShdr out (shstrtab.off ".rodata") 1 2 rodataOff.toUInt64 rodataOff.toUInt64 rodataSize.toUInt64 0 0 8 0
  -- .dynsym, .dynstr, .rel.dyn, .dynamic
  if hasDynamic then
    -- .dynsym: SHT_DYNSYM (11), SHF_ALLOC (2), link=dynstrShIdx, info=1 (first non-local), entsize=24
    out := pushShdr out (shstrtab.off ".dynsym") 11 2 dynsymOff.toUInt64 dynsymOff.toUInt64 dynsymBytes.size.toUInt64 dynstrShIdx.toUInt32 1 8 24
    -- .dynstr: SHT_STRTAB (3), SHF_ALLOC (2)
    out := pushShdr out (shstrtab.off ".dynstr") 3 2 dynstrOff.toUInt64 dynstrOff.toUInt64 dynstr.bytes.size.toUInt64 0 0 1 0
    -- .rel.dyn: SHT_REL (9), SHF_ALLOC (2), link=dynsymShIdx, entsize=16
    out := pushShdr out (shstrtab.off ".rel.dyn") 9 2 relDynOff.toUInt64 relDynOff.toUInt64 relDynBytes.size.toUInt64 dynsymShIdx.toUInt32 0 8 16
    -- .dynamic: SHT_DYNAMIC (6), SHF_WRITE|SHF_ALLOC (3), link=dynstrShIdx, entsize=16
    out := pushShdr out (shstrtab.off ".dynamic") 6 3 dynamicOff.toUInt64 dynamicOff.toUInt64 dynamicBytes.size.toUInt64 dynstrShIdx.toUInt32 0 8 16
  -- .shstrtab: SHT_STRTAB (3)
  out := pushShdr out (shstrtab.off ".shstrtab") 3 0 0 shstrtabOff.toUInt64 shstrtab.bytes.size.toUInt64 0 0 1 0

  return (out, asm)

/-- Emit a strict next-gen Solana SBPF V3 ELF64 `.so` (`EM_SBPF = 263`, `e_flags = 3`,
    static syscalls, 4 program headers, 0 relocations). -/
def emitElfV3 (insns : Array Insn) (rodata : ByteArray) (stackBytes : Nat := 4096) :
    Except String (ByteArray × AssembledText) := do
  -- SBPF V3 requires entry instruction to be a function-start marker (`add64 r10, -stack` or `add64 r10, 0`)
  let v3Insns := #[Insn.alu64Imm .add Reg.r10 0] ++ insns
  let asm ← assemble v3Insns .v3 0x100000000
  let rodataPadded := if rodata.size == 0 then ByteArray.empty.push 0 else rodata

  let textOff : Nat := alignUp (64 + 56 * 4) 8 -- 64 + 224 = 288
  let textSize : Nat := asm.bytes.size
  let rodataOff : Nat := alignUp (textOff + textSize) 8
  let rodataSize : Nat := rodataPadded.size

  let shstrtab := buildStrTab [".text", ".rodata", ".shstrtab"]
  let shstrtabOff := alignUp (rodataOff + rodataSize) 8
  let shoff := alignUp (shstrtabOff + shstrtab.bytes.size) 8

  let mut out := ByteArray.emptyWithCapacity (shoff + 4 * 64)
  -- EM_SBPF = 263, e_entry = 0 (MM_BYTECODE_START), e_flags = 3 (V3), 4 phdrs, 4 shdrs, shstrndx = 3
  out := pushEhdr out 263 0 64 shoff.toUInt64 3 4 4 3

  -- 4 Strict Program Headers required by SBPF V3 loader:
  -- 0: PF_X (1) @ MM_BYTECODE_START (0x0)
  out := pushPhdr out 1 1 textOff.toUInt64 0 0 textSize.toUInt64 textSize.toUInt64 8
  -- 1: PF_R (4) @ MM_RODATA_START (0x100000000)
  out := pushPhdr out 1 4 rodataOff.toUInt64 0x100000000 0x100000000 rodataSize.toUInt64 rodataSize.toUInt64 8
  -- 2: PF_R|PF_W (6) @ MM_STACK_START (0x200000000), filesz = 0
  let stackMemsz := (max 4096 stackBytes).toUInt64
  out := pushPhdr out 1 6 0 0x200000000 0x200000000 0 stackMemsz 8
  -- 3: PF_R|PF_W (6) @ MM_HEAP_START (0x300000000), filesz = 0, memsz = 0 (ZERO HEAP!)
  out := pushPhdr out 1 6 0 0x300000000 0x300000000 0 0 8

  out := padTo out textOff
  out := out ++ asm.bytes
  out := padTo out rodataOff
  out := out ++ rodataPadded
  out := padTo out shstrtabOff
  out := out ++ shstrtab.bytes
  out := padTo out shoff

  -- Section Headers: [0] NULL, [1] .text, [2] .rodata, [3] .shstrtab
  out := pushShdr out 0 0 0 0 0 0 0 0 0 0
  out := pushShdr out (shstrtab.off ".text") 1 6 0 textOff.toUInt64 textSize.toUInt64 0 0 8 0
  out := pushShdr out (shstrtab.off ".rodata") 1 2 0x100000000 rodataOff.toUInt64 rodataSize.toUInt64 0 0 8 0
  out := pushShdr out (shstrtab.off ".shstrtab") 3 0 0 shstrtabOff.toUInt64 shstrtab.bytes.size.toUInt64 0 0 1 0

  return (out, asm)

/-- Emit a Solana sBPF ELF64 `.so` binary targeting `ver` (`.v0` or `.v3`). -/
def emitElf (insns : Array Insn) (rodata : ByteArray) (ver : Version := .v0) :
    Except String (ByteArray × AssembledText) :=
  match ver with
  | .v0 => emitElfV0 insns rodata
  | .v3 => emitElfV3 insns rodata

end LeanSVM.SBPF
