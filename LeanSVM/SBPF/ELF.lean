/-
  LeanSVM.SBPF.ELF
  Direct native Lean 4 ELF64 shared-object (.so) linker and serializer for Solana sBPF v3
  (SIMD-0178 static syscalls + SIMD-0189 strict ELF headers + SIMD-0377 / SIMD-0500).

  Produces minimal, zero-bloat `.so` binaries accepted directly by Solana Mainnet, Devnet,
  Testnet, Agave 4.x, and LiteSVM:
  - `e_machine = EM_BPF (247)`, `e_flags = 3` (`SBPFVersion::V3`), `e_entry = 0x100000000`
  - Strict contiguous 8-byte-aligned `PT_LOAD` program headers (1 PHDR if `.rodata` is empty,
    2 PHDRs if `.rodata` is non-empty), zero dynamic tables, zero relocations!
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
def pushEhdr (buf : ByteArray)
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
  let b := pushU16LE b eMachine   -- e_machine = EM_BPF (247)
  let b := pushU32LE b 1          -- e_version = EV_CURRENT
  let b := pushU64LE b eEntry     -- e_entry
  let b := pushU64LE b ePhoff     -- e_phoff
  let b := pushU64LE b eShoff     -- e_shoff
  let b := pushU32LE b eFlags     -- e_flags (3 = SBPFVersion::V3)
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

/-- Emit a shipping Solana sBPF v3 ELF64 `.so` conforming strictly to SIMD-0178, SIMD-0189,
    SIMD-0377, and SIMD-0500 (`solana-sbpf >= 0.23` / Agave 4.x / mainnet-beta):
    - `e_machine = EM_BPF (247)`, `e_flags = 3` (`SBPFVersion::V3`), `e_entry = 0x100000000`
    - Strict contiguous 8-byte-aligned `PT_LOAD` program headers (`expected_offset` exact):
      * If `rodata.size > 0` (`e_phnum = 2`):
        - PHDR `[0]`: `PF_R (4)` @ `MM_RODATA_START (0x0)` (prefixed with 8 zero bytes so no
          `.rodata` pointer is ever NULL `0x0`, and padded to an exact 8-byte multiple!)
        - PHDR `[1]`: `PF_X (1)` @ `MM_BYTECODE_START (0x100000000)`
      * If `rodata.size == 0` (`e_phnum = 1`):
        - PHDR `[0]`: `PF_X (1)` @ `MM_BYTECODE_START (0x100000000)`
    - Zero dynamic tables, zero relocations, static Murmur3-32 syscalls! -/
def emitElf (insns : Array Insn) (rodata : ByteArray) :
    Except String (ByteArray × AssembledText) := do
  let hasRodata := rodata.size > 0
  -- When `.rodata` is present, reserve 8 leading zero bytes at VA 0x0 so real rodata starts at VA 0x8
  -- (never NULL!) and pad total `.rodata` filesz to an exact 8-byte multiple (SIMD-0189 requirement).
  let rodataPadded : ByteArray :=
    if hasRodata then
      let prefixed := ByteArray.mk (Array.replicate 8 0) ++ rodata
      padTo prefixed (alignUp prefixed.size 8)
    else
      ByteArray.empty
  let rodataBaseVaddr : UInt64 := if hasRodata then 8 else 0
  let asm ← assemble insns rodataBaseVaddr

  let phnum : Nat := if hasRodata then 2 else 1
  let phEnd : Nat := 64 + 56 * phnum -- 120 (1 PHDR) or 176 (2 PHDRs): both 8-byte aligned!
  let rodataOff : Nat := phEnd
  let rodataSize : Nat := rodataPadded.size
  let textOff : Nat := phEnd + rodataSize
  let textSize : Nat := asm.bytes.size

  let shNames : List String :=
    if hasRodata then [".rodata", ".text", ".shstrtab"]
    else [".text", ".shstrtab"]
  let shstrtab := buildStrTab shNames
  let shstrtabOff := alignUp (textOff + textSize) 8
  let shoff := alignUp (shstrtabOff + shstrtab.bytes.size) 8
  let shnum : Nat := if hasRodata then 4 else 3
  let shstrndx : Nat := shnum - 1

  let mut out := ByteArray.emptyWithCapacity (shoff + shnum * 64)
  -- EM_BPF = 247, e_entry = 0x100000000 (MM_BYTECODE_START), e_phoff = 64, e_flags = 3 (SBPFVersion::V3)
  out := pushEhdr out 247 0x100000000 64 shoff.toUInt64 3 phnum.toUInt16 shnum.toUInt16 shstrndx.toUInt16

  -- Strict SIMD-0189 Program Headers (contiguous starting immediately at phEnd):
  if hasRodata then
    -- [0] PF_R (4) @ MM_RODATA_START (0x0)
    out := pushPhdr out 1 4 rodataOff.toUInt64 0 0 rodataSize.toUInt64 rodataSize.toUInt64 8
  -- [0 or 1] PF_X (1) @ MM_BYTECODE_START (0x100000000)
  out := pushPhdr out 1 1 textOff.toUInt64 0x100000000 0x100000000 textSize.toUInt64 textSize.toUInt64 8

  if hasRodata then
    out := out ++ rodataPadded
  out := out ++ asm.bytes
  out := padTo out shstrtabOff
  out := out ++ shstrtab.bytes
  out := padTo out shoff

  -- Section Headers (for readelf / tooling compatibility; optional to SIMD-0189 loader):
  -- [0] NULL
  out := pushShdr out 0 0 0 0 0 0 0 0 0 0
  if hasRodata then
    -- [1] .rodata: SHT_PROGBITS (1), SHF_ALLOC (2) @ 0x0
    out := pushShdr out (shstrtab.off ".rodata") 1 2 0 rodataOff.toUInt64 rodataSize.toUInt64 0 0 8 0
  -- .text: SHT_PROGBITS (1), SHF_ALLOC|SHF_EXECINSTR (6) @ 0x100000000
  out := pushShdr out (shstrtab.off ".text") 1 6 0x100000000 textOff.toUInt64 textSize.toUInt64 0 0 8 0
  -- .shstrtab: SHT_STRTAB (3)
  out := pushShdr out (shstrtab.off ".shstrtab") 3 0 0 shstrtabOff.toUInt64 shstrtab.bytes.size.toUInt64 0 0 1 0

  return (out, asm)

/-- `pushEhdr` ALWAYS appends exact 64 bytes (`sizeof(Elf64_Ehdr)`). -/
theorem pushEhdr_size (buf : ByteArray)
    (eMachine : UInt16) (eEntry ePhoff eShoff : UInt64)
    (eFlags : UInt32) (ePhnum eShnum eShstrndx : UInt16) :
    (pushEhdr buf eMachine eEntry ePhoff eShoff eFlags ePhnum eShnum eShstrndx).size =
      buf.size + 64 := by
  simp only [pushEhdr, pushU16LE, pushU32LE, pushU64LE, ByteArray.size_push]

end LeanSVM.SBPF
