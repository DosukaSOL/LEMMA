/-
  LeanSVM.SBPF.ISA
  Native Solana sBPF (V0 & V3) Instruction Set Architecture, exact 8-byte little-endian
  machine code encoder, Murmur3-32 static syscall hasher, and built-in disassembler.
-/

namespace LeanSVM.SBPF

/-- Target Solana SBPF ISA version. -/
inductive Version where
  | v0  -- Classic Solana sBPF (mainnet/devnet/Agave/LiteSVM universal default)
  | v3  -- Strict SBPFv3 (static syscalls, PQR ops, zero relocations)
  deriving Repr, BEq, DecidableEq

/-- Physical sBPF registers (`r0`..`r10`).
    - `r0`: return value / scratch
    - `r1..r5`: arguments / caller-saved scratch
    - `r6..r9`: callee-saved (preserved across syscalls & internal calls)
    - `r10`: read-only stack frame pointer -/
structure Reg where
  idx : UInt8
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

namespace Reg
  def r0  : Reg := ⟨0⟩
  def r1  : Reg := ⟨1⟩
  def r2  : Reg := ⟨2⟩
  def r3  : Reg := ⟨3⟩
  def r4  : Reg := ⟨4⟩
  def r5  : Reg := ⟨5⟩
  def r6  : Reg := ⟨6⟩
  def r7  : Reg := ⟨7⟩
  def r8  : Reg := ⟨8⟩
  def r9  : Reg := ⟨9⟩
  def r10 : Reg := ⟨10⟩

  def toString (r : Reg) : String := s!"r{r.idx}"
  instance : ToString Reg := ⟨Reg.toString⟩
end Reg

/-- Memory access width in bytes. -/
inductive MemSize where
  | b1 | b2 | b4 | b8
  deriving Repr, BEq, DecidableEq

/-- ALU operation code. -/
inductive AluOp where
  | add | sub | mul | div | or | and | lsh | rsh | mod | xor | mov | arsh
  deriving Repr, BEq, DecidableEq

/-- True iff Solana sBPF (both v0 and v3) sign-extends the 32-bit result of `op` into
    bits `32..63` (`i32 → i64 → u64`) instead of zero-extending (`u32 → u64`). -/
def AluOp.signExtendsInAlu32 : AluOp → Bool
  | .add | .sub | .mul => true
  | _ => false

/-- Conditional jump predicate. -/
inductive JmpCond where
  | eq | gt | ge | set | ne | sgt | sge | lt | le | slt | sle
  deriving Repr, BEq, DecidableEq

namespace JmpCond
  /-- Logical negation of a branch condition (used for fallthrough optimization). -/
  def invert : JmpCond → Option JmpCond
    | .eq  => some .ne
    | .ne  => some .eq
    | .gt  => some .le
    | .le  => some .gt
    | .ge  => some .lt
    | .lt  => some .ge
    | .sgt => some .sle
    | .sle => some .sgt
    | .sge => some .slt
    | .slt => some .sge
    | .set => none

  def mnemonic : JmpCond → String
    | .eq  => "jeq"
    | .gt  => "jgt"
    | .ge  => "jge"
    | .set => "jset"
    | .ne  => "jne"
    | .sgt => "jsgt"
    | .sge => "jsge"
    | .lt  => "jlt"
    | .le  => "jle"
    | .slt => "jslt"
    | .sle => "jsle"
end JmpCond

/-- Symbolic sBPF instruction (before label offset resolution). -/
inductive Insn where
  | label (name : String)
  | alu64Reg (op : AluOp) (dst src : Reg)
  | alu64Imm (op : AluOp) (dst : Reg) (imm : Int32)
  | alu32Reg (op : AluOp) (dst src : Reg)
  | alu32Imm (op : AluOp) (dst : Reg) (imm : Int32)
  | neg64 (dst : Reg)
  | lddw (dst : Reg) (imm : UInt64)
  | lddwRodata (dst : Reg) (rodataOff : UInt32)
  | ldx (sz : MemSize) (dst src : Reg) (off : Int16)
  | stx (sz : MemSize) (dst src : Reg) (off : Int16)
  | stImm (sz : MemSize) (dst : Reg) (off : Int16) (imm : Int32)
  | ja (target : String)
  | jccReg (cond : JmpCond) (dst src : Reg) (target : String)
  | jccImm (cond : JmpCond) (dst : Reg) (imm : Int32) (target : String)
  | callLocal (target : String)
  | callSyscall (symName : String)
  | exit
  deriving Repr, BEq, Inhabited

/-- Number of 8-byte sBPF instruction slots occupied by an instruction. -/
def Insn.slotCount (ver : Version := .v0) : Insn → Nat
  | .label _       => 0
  | .lddw _ _      => 2
  | .lddwRodata _ _ => 2
  | _              =>
    let _ := ver
    1

/-! ### Little-Endian ByteArray Encoding Helpers -/

def pushU16LE (buf : ByteArray) (v : UInt16) : ByteArray :=
  buf
    |>.push (v &&& 0xFF).toUInt8
    |>.push ((v >>> 8) &&& 0xFF).toUInt8

def pushU32LE (buf : ByteArray) (v : UInt32) : ByteArray :=
  buf
    |>.push (v &&& 0xFF).toUInt8
    |>.push ((v >>> 8) &&& 0xFF).toUInt8
    |>.push ((v >>> 16) &&& 0xFF).toUInt8
    |>.push ((v >>> 24) &&& 0xFF).toUInt8

def pushU64LE (buf : ByteArray) (v : UInt64) : ByteArray :=
  let lo := v.toUInt32
  let hi := (v >>> 32).toUInt32
  pushU32LE (pushU32LE buf lo) hi

/-- Encode one 8-byte raw sBPF instruction word: `[opc, (src<<4)|dst, off_lo, off_hi, imm0..3]`. -/
def pushRawInsn (buf : ByteArray) (opc : UInt8) (dst src : UInt8) (off : Int16) (imm : UInt32) : ByteArray :=
  let regs : UInt8 := ((src &&& 0x0F) <<< 4) ||| (dst &&& 0x0F)
  let offU : UInt16 := off.toUInt16
  let b1 := buf.push opc |>.push regs
  let b2 := pushU16LE b1 offU
  pushU32LE b2 imm

/-! ### Exact Solana sBPF Opcode Tables -/

def aluBaseOpc : AluOp → UInt8
  | .add  => 0x00
  | .sub  => 0x10
  | .mul  => 0x20
  | .div  => 0x30
  | .or   => 0x40
  | .and  => 0x50
  | .lsh  => 0x60
  | .rsh  => 0x70
  | .mod  => 0x90
  | .xor  => 0xa0
  | .mov  => 0xb0
  | .arsh => 0xc0

private def jmpBaseOpc : JmpCond → UInt8
  | .eq  => 0x10
  | .gt  => 0x20
  | .ge  => 0x30
  | .set => 0x40
  | .ne  => 0x50
  | .sgt => 0x60
  | .sge => 0x70
  | .lt  => 0xa0
  | .le  => 0xb0
  | .slt => 0xc0
  | .sle => 0xd0

def ldxOpc (ver : Version) : MemSize → UInt8
  | .b1 => match ver with | .v0 => 0x71 | .v3 => 0x2c
  | .b2 => match ver with | .v0 => 0x69 | .v3 => 0x3c
  | .b4 => match ver with | .v0 => 0x61 | .v3 => 0x8c
  | .b8 => match ver with | .v0 => 0x79 | .v3 => 0x9c

def stxOpc (ver : Version) : MemSize → UInt8
  | .b1 => match ver with | .v0 => 0x73 | .v3 => 0x2f
  | .b2 => match ver with | .v0 => 0x6b | .v3 => 0x3f
  | .b4 => match ver with | .v0 => 0x63 | .v3 => 0x8f
  | .b8 => match ver with | .v0 => 0x7b | .v3 => 0x9f

def stImmOpc (ver : Version) : MemSize → UInt8
  | .b1 => match ver with | .v0 => 0x72 | .v3 => 0x27
  | .b2 => match ver with | .v0 => 0x6a | .v3 => 0x37
  | .b4 => match ver with | .v0 => 0x62 | .v3 => 0x87
  | .b8 => match ver with | .v0 => 0x7a | .v3 => 0x97

def alu64RegOpc (ver : Version) (op : AluOp) : UInt8 :=
  match ver, op with
  | .v3, .mul => 0x9e  -- LMUL64_REG (BPF_PQR | BPF_B | BPF_X | BPF_LMUL)
  | .v3, .div => 0x5e  -- UDIV64_REG
  | .v3, .mod => 0x7e  -- UREM64_REG
  | _,   _    => aluBaseOpc op ||| 0x0f -- BPF_ALU64 | BPF_X

def alu64ImmOpc (ver : Version) (op : AluOp) : UInt8 :=
  match ver, op with
  | .v3, .mul => 0x96  -- LMUL64_IMM
  | .v3, .div => 0x56  -- UDIV64_IMM
  | .v3, .mod => 0x76  -- UREM64_IMM
  | _,   _    => aluBaseOpc op ||| 0x07 -- BPF_ALU64 | BPF_K

def alu32RegOpc (ver : Version) (op : AluOp) : UInt8 :=
  match ver, op with
  | .v3, .mul => 0x8e  -- LMUL32_REG
  | .v3, .div => 0x4e  -- UDIV32_REG
  | .v3, .mod => 0x6e  -- UREM32_REG
  | _,   _    => aluBaseOpc op ||| 0x0c -- BPF_ALU32 | BPF_X

def alu32ImmOpc (ver : Version) (op : AluOp) : UInt8 :=
  match ver, op with
  | .v3, .mul => 0x86  -- LMUL32_IMM
  | .v3, .div => 0x46  -- UDIV32_IMM
  | .v3, .mod => 0x66  -- UREM32_IMM
  | _,   _    => aluBaseOpc op ||| 0x04 -- BPF_ALU32 | BPF_K

/-- Opcode for unary 64-bit negation (`dst = -dst`):
    - sBPF v0: `0x87` (`NEG64`)
    - sBPF v3: `0x17` (`SUB64_IMM dst, 0` computes `0 - dst` under SIMD-0174, avoiding the
      reassigned `0x87 = ST_4B_IMM` opcode removed by SIMD-0173!). -/
def neg64Opc (ver : Version) : UInt8 :=
  match ver with
  | .v0 => 0x87
  | .v3 => 0x17

/-! ### Murmur3-32 Hasher (exact match to Solana `ebpf::hash_symbol_name`) -/

private def rotl32 (x : UInt32) (r : UInt32) : UInt32 :=
  (x <<< r) ||| (x >>> (32 - r))

/-- Exact Murmur3-32 (seed = 0) matching Solana `solana_sbpf::ebpf::hash_symbol_name`. -/
def murmur3_32 (bytes : ByteArray) : UInt32 := Id.run do
  let len := bytes.size
  let nblocks := len / 4
  let c1 : UInt32 := 0xcc9e2d51
  let c2 : UInt32 := 0x1b873593
  let mut h1 : UInt32 := 0
  for i in [0:nblocks] do
    let b := i * 4
    let k0 := (bytes.get! b).toUInt32
    let k1 := (bytes.get! (b + 1)).toUInt32 <<< 8
    let k2 := (bytes.get! (b + 2)).toUInt32 <<< 16
    let k3 := (bytes.get! (b + 3)).toUInt32 <<< 24
    let mut k := k0 ||| k1 ||| k2 ||| k3
    k := k * c1
    k := rotl32 k 15
    k := k * c2
    h1 := h1 ^^^ k
    h1 := rotl32 h1 13
    h1 := h1 * 5 + 0xe6546b64
  let tail := nblocks * 4
  let rem := len - tail
  let mut k1 : UInt32 := 0
  if rem >= 3 then k1 := k1 ^^^ ((bytes.get! (tail + 2)).toUInt32 <<< 16)
  if rem >= 2 then k1 := k1 ^^^ ((bytes.get! (tail + 1)).toUInt32 <<< 8)
  if rem >= 1 then
    k1 := k1 ^^^ (bytes.get! tail).toUInt32
    k1 := k1 * c1
    k1 := rotl32 k1 15
    k1 := k1 * c2
    h1 := h1 ^^^ k1
  h1 := h1 ^^^ len.toUInt32
  h1 := h1 ^^^ (h1 >>> 16)
  h1 := h1 * 0x85ebca6b
  h1 := h1 ^^^ (h1 >>> 13)
  h1 := h1 * 0xc2b2ae35
  h1 := h1 ^^^ (h1 >>> 16)
  return h1

def hashSyscallName (name : String) : UInt32 :=
  murmur3_32 name.toUTF8

/-! ### Assembler (2-pass label resolution -> raw `.text` + syscall relocations) -/

/-- Relocation record for V0 external syscall calls (`R_BPF_64_32`). -/
structure SyscallReloc where
  /-- Byte offset within `.text` of the `call -1` instruction. -/
  textByteOffset : UInt64
  /-- Syscall symbol name (e.g. `"sol_log_"`). -/
  symName : String
  deriving Repr, BEq

/-- Relocation record for `.rodata` pointer loads (optional; we also embed direct MM_RODATA_START VA). -/
structure RodataFixup where
  /-- Byte offset within `.text` of the `lddw` instruction. -/
  textByteOffset : UInt64
  /-- Byte offset within `.rodata`. -/
  rodataOff : UInt32
  deriving Repr, BEq

/-- Result of assembling a symbolic sBPF instruction list. -/
structure AssembledText where
  bytes         : ByteArray
  insnCount     : Nat
  syscallRelocs : Array SyscallReloc
  rodataFixups  : Array RodataFixup

/-- Assemble symbolic `Array Insn` into `.text` bytecode.
    `rodataBaseVaddr` is the exact VM virtual address of `.rodata` (`0x100000000 + rodataShOffset` for V0,
    `0x100000000` for V3). -/
def assemble (insns : Array Insn) (ver : Version := .v0) (rodataBaseVaddr : UInt64 := 0x100000000) :
    Except String AssembledText := do
  -- Pass 1: record PC (in 8-byte instruction slots) of each label
  let mut labelPc : List (String × Nat) := []
  let mut pc : Nat := 0
  for insn in insns do
    match insn with
    | .label name => labelPc := (name, pc) :: labelPc
    | _ => pc := pc + insn.slotCount ver
  let findLabel (name : String) : Except String Nat :=
    match labelPc.find? (fun p => p.1 == name) with
    | some (_, targetPc) => .ok targetPc
    | none => .error s!"undefined sBPF label: {name}"
  -- Pass 2: encode every instruction
  let mut buf := ByteArray.emptyWithCapacity (pc * 8)
  let mut relocs : Array SyscallReloc := #[]
  let mut roFixups : Array RodataFixup := #[]
  let mut curPc : Nat := 0
  for insn in insns do
    match insn with
    | .label _ => pure ()
    | .alu64Reg op dst src =>
      buf := pushRawInsn buf (alu64RegOpc ver op) dst.idx src.idx 0 0
      curPc := curPc + 1
    | .alu64Imm op dst imm =>
      if ver == .v3 && op == .sub then
        -- Under sBPF v2/v3 (SIMD-0174), `SUB64_IMM` (0x17) computes `imm - dst` rather than `dst - imm`.
        -- Rewrite `dst - imm` into `ADD64_IMM dst, (-imm)` when `-imm` fits in Int32; reject `Int32.minValue`.
        if imm.toInt == -2147483648 then
          throw "sBPF v3: alu64Imm .sub with Int32.minValue cannot be lowered in 1 slot"
        let negImm : Int32 := Int32.ofInt (-imm.toInt)
        buf := pushRawInsn buf (alu64ImmOpc ver .add) dst.idx 0 0 negImm.toUInt32
      else
        buf := pushRawInsn buf (alu64ImmOpc ver op) dst.idx 0 0 imm.toUInt32
      curPc := curPc + 1
    | .alu32Reg op dst src =>
      buf := pushRawInsn buf (alu32RegOpc ver op) dst.idx src.idx 0 0
      curPc := curPc + 1
    | .alu32Imm op dst imm =>
      if ver == .v3 && op == .sub then
        -- Under sBPF v2/v3 (SIMD-0174), `SUB32_IMM` (0x14) computes `imm - dst`.
        if imm.toInt == -2147483648 then
          throw "sBPF v3: alu32Imm .sub with Int32.minValue cannot be lowered in 1 slot"
        let negImm : Int32 := Int32.ofInt (-imm.toInt)
        buf := pushRawInsn buf (alu32ImmOpc ver .add) dst.idx 0 0 negImm.toUInt32
      else
        buf := pushRawInsn buf (alu32ImmOpc ver op) dst.idx 0 0 imm.toUInt32
      curPc := curPc + 1
    | .neg64 dst =>
      buf := pushRawInsn buf (neg64Opc ver) dst.idx 0 0 0
      curPc := curPc + 1
    | .lddw dst imm =>
      match ver with
      | .v0 =>
        let lo := imm.toUInt32
        let hi := (imm >>> 32).toUInt32
        buf := pushRawInsn buf 0x18 dst.idx 0 0 lo
        buf := pushRawInsn buf 0x00 0 0 0 hi
        curPc := curPc + 2
      | .v3 =>
        let lo := imm.toUInt32
        let hi := (imm >>> 32).toUInt32
        -- mov32 zero-extends lo, then hor64 ORs hi << 32
        buf := pushRawInsn buf 0xb4 dst.idx 0 0 lo
        buf := pushRawInsn buf 0xf7 dst.idx 0 0 hi
        curPc := curPc + 2
    | .lddwRodata dst roOff =>
      let va := rodataBaseVaddr + roOff.toUInt64
      roFixups := roFixups.push { textByteOffset := (curPc * 8).toUInt64, rodataOff := roOff }
      match ver with
      | .v0 =>
        let lo := va.toUInt32
        let hi := (va >>> 32).toUInt32
        buf := pushRawInsn buf 0x18 dst.idx 0 0 lo
        buf := pushRawInsn buf 0x00 0 0 0 hi
        curPc := curPc + 2
      | .v3 =>
        let lo := va.toUInt32
        let hi := (va >>> 32).toUInt32
        buf := pushRawInsn buf 0xb4 dst.idx 0 0 lo
        buf := pushRawInsn buf 0xf7 dst.idx 0 0 hi
        curPc := curPc + 2
    | .ldx sz dst src off =>
      buf := pushRawInsn buf (ldxOpc ver sz) dst.idx src.idx off 0
      curPc := curPc + 1
    | .stx sz dst src off =>
      buf := pushRawInsn buf (stxOpc ver sz) dst.idx src.idx off 0
      curPc := curPc + 1
    | .stImm sz dst off imm =>
      buf := pushRawInsn buf (stImmOpc ver sz) dst.idx 0 off imm.toUInt32
      curPc := curPc + 1
    | .ja target =>
      let tPc ← findLabel target
      let delta : Int := (tPc : Int) - ((curPc + 1 : Nat) : Int)
      if delta < -32768 || delta > 32767 then
        throw s!"jump offset out of Int16 range for label {target}: {delta}"
      buf := pushRawInsn buf 0x05 0 0 (Int16.ofInt delta) 0
      curPc := curPc + 1
    | .jccReg cond dst src target =>
      let tPc ← findLabel target
      let delta : Int := (tPc : Int) - ((curPc + 1 : Nat) : Int)
      if delta < -32768 || delta > 32767 then
        throw s!"branch offset out of Int16 range for label {target}: {delta}"
      let opc := jmpBaseOpc cond ||| 0x0d -- BPF_JMP | BPF_X
      buf := pushRawInsn buf opc dst.idx src.idx (Int16.ofInt delta) 0
      curPc := curPc + 1
    | .jccImm cond dst imm target =>
      let tPc ← findLabel target
      let delta : Int := (tPc : Int) - ((curPc + 1 : Nat) : Int)
      if delta < -32768 || delta > 32767 then
        throw s!"branch offset out of Int16 range for label {target}: {delta}"
      let opc := jmpBaseOpc cond ||| 0x05 -- BPF_JMP | BPF_K
      buf := pushRawInsn buf opc dst.idx 0 (Int16.ofInt delta) imm.toUInt32
      curPc := curPc + 1
    | .callLocal target =>
      let tPc ← findLabel target
      let delta : Int := (tPc : Int) - ((curPc + 1 : Nat) : Int)
      let srcField : UInt8 := match ver with | .v0 => 1 | .v3 => 0
      -- In V0: CALL_IMM (0x85) with imm != -1 is a PC-relative internal call
      -- In V3: CALL_IMM (0x85) with src=0 is a PC-relative internal call
      buf := pushRawInsn buf 0x85 0 srcField 0 (Int32.ofInt delta).toUInt32
      curPc := curPc + 1
    | .callSyscall symName =>
      match ver with
      | .v0 =>
        relocs := relocs.push { textByteOffset := (curPc * 8).toUInt64, symName }
        buf := pushRawInsn buf 0x85 0 0 0 0xFFFFFFFF
        curPc := curPc + 1
      | .v3 =>
        let h := hashSyscallName symName
        buf := pushRawInsn buf 0x95 0 0 0 h
        curPc := curPc + 1
    | .exit =>
      let opc : UInt8 := match ver with | .v0 => 0x95 | .v3 => 0x9d
      buf := pushRawInsn buf opc 0 0 0 0
      curPc := curPc + 1
  return { bytes := buf, insnCount := curPc, syscallRelocs := relocs, rodataFixups := roFixups }

/-! ### Built-In sBPF Disassembler -/

private def aluMnemonic : AluOp → String
  | .add  => "add"
  | .sub  => "sub"
  | .mul  => "mul"
  | .div  => "div"
  | .or   => "or"
  | .and  => "and"
  | .lsh  => "lsh"
  | .rsh  => "rsh"
  | .mod  => "mod"
  | .xor  => "xor"
  | .mov  => "mov"
  | .arsh => "arsh"

private def szSuffix : MemSize → String
  | .b1 => "b"
  | .b2 => "h"
  | .b4 => "w"
  | .b8 => "dw"

private def fmtOff (off : Int16) : String :=
  let i := off.toInt
  if i >= 0 then s!"+{i}" else s!"{i}"

def formatInsn : Insn → String
  | .label name             => s!"{name}:"
  | .alu64Reg op d s        => s!"  {aluMnemonic op}64 {d}, {s}"
  | .alu64Imm op d imm      => s!"  {aluMnemonic op}64 {d}, {imm}"
  | .alu32Reg op d s        => s!"  {aluMnemonic op}32 {d}, {s}"
  | .alu32Imm op d imm      => s!"  {aluMnemonic op}32 {d}, {imm}"
  | .neg64 d                => s!"  neg64 {d}"
  | .lddw d imm             => s!"  lddw {d}, 0x{String.ofList (Nat.toDigits 16 imm.toNat)}"
  | .lddwRodata d off       => s!"  lddw {d}, .rodata+{off}"
  | .ldx sz d s off         => s!"  ldx{szSuffix sz} {d}, [{s}{fmtOff off}]"
  | .stx sz d s off         => s!"  stx{szSuffix sz} [{d}{fmtOff off}], {s}"
  | .stImm sz d off imm     => s!"  st{szSuffix sz} [{d}{fmtOff off}], {imm}"
  | .ja tgt                 => s!"  ja {tgt}"
  | .jccReg c d s tgt       => s!"  {c.mnemonic} {d}, {s}, {tgt}"
  | .jccImm c d imm tgt     => s!"  {c.mnemonic} {d}, {imm}, {tgt}"
  | .callLocal tgt          => s!"  call {tgt}"
  | .callSyscall sym        => s!"  syscall {sym}"
  | .exit                   => "  exit"

def formatProgram (insns : Array Insn) : String :=
  String.intercalate "\n" (insns.toList.map formatInsn)

end LeanSVM.SBPF
