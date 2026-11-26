/-
  LemmaTest.Sbpf — an independent, executable sBPF v0 interpreter used as a TEST ORACLE.

  Why this exists: the LiteSVM runner needs crates.io, which may be unavailable. This interpreter
  executes the *symbolic* instruction stream produced by the real lean-svm compiler pipeline
  (`compileEntrypoint`), so compiled behaviour can be compared against the Lean definitions.

  What it is NOT:
  * not Agave / rbpf — it does not check the ELF encoding, the verifier, or exact CU costs;
  * not a proof — it is ordinary (unverified) test code.
  Results from it are labelled "interpreter" and never substitute for LiteSVM runs.

  Deliberate strictness (stricter than the real VM, so compiler bugs surface rather than hide):
  * after every syscall, r1..r5 are overwritten with garbage (they are caller-saved);
  * reads of never-written stack bytes return a poison pattern (0xA5);
  * any access outside the mapped input / stack / rodata regions is an access violation.
-/
import LeanSVM
import Std.Data.HashMap

namespace LemmaTest.Sbpf
open LeanSVM.SBPF

/-- Virtual-memory layout (matches Agave's `MM_*` constants). -/
def rodataStart : UInt64 := 0x100000000
def stackStart  : UInt64 := 0x200000000
def inputStart  : UInt64 := 0x400000000
def frameSize   : UInt64 := 4096
def maxFrames   : Nat    := 64

inductive Halt where
  | exit (r0 : UInt64)
  | abort                      -- `abort` syscall
  | divByZero (pc : Nat)
  | accessViolation (addr : UInt64) (pc : Nat)
  | callDepthExceeded
  | outOfFuel
  | badJump (label : String)
  | unsupportedSyscall (name : String)
  | badInsn (pc : Nat)
  deriving Repr, BEq, Inhabited

structure Frame where
  retPc : Nat
  saved : Array UInt64   -- r6..r9
  fp    : UInt64

structure St where
  regs   : Array UInt64          -- r0..r10
  mem    : Std.HashMap UInt64 UInt8
  inputLen : UInt64
  rodataLen : UInt64
  frames : List Frame
  logs   : Array String
  steps  : Nat

def St.reg (s : St) (r : Reg) : UInt64 := s.regs[r.idx.toNat]!
def St.set (s : St) (r : Reg) (v : UInt64) : St := { s with regs := s.regs.set! r.idx.toNat v }

/-- Is `[addr, addr+n)` inside a mapped region? Writes are not allowed to rodata. -/
def St.mapped (s : St) (addr : UInt64) (n : Nat) (write : Bool) : Bool :=
  let n64 := n.toUInt64
  let inRange (lo len : UInt64) := lo ≤ addr && addr + n64 ≤ lo + len && addr + n64 ≥ addr
  inRange inputStart s.inputLen ||
  inRange stackStart (frameSize * maxFrames.toUInt64) ||
  (!write && inRange rodataStart s.rodataLen)

def St.readByte (s : St) (a : UInt64) : UInt8 := s.mem.getD a 0xA5

def St.load (s : St) (addr : UInt64) (n : Nat) : UInt64 := Id.run do
  let mut v : UInt64 := 0
  for i in [0:n] do
    v := v ||| ((s.readByte (addr + i.toUInt64)).toUInt64 <<< (8 * i).toUInt64)
  return v

def St.store (s : St) (addr : UInt64) (n : Nat) (v : UInt64) : St := Id.run do
  let mut m := s.mem
  for i in [0:n] do
    m := m.insert (addr + i.toUInt64) ((v >>> (8 * i).toUInt64) &&& 0xFF).toUInt8
  return { s with mem := m }

def sizeBytes : MemSize → Nat
  | .b1 => 1 | .b2 => 2 | .b4 => 4 | .b8 => 8

def sext32 (i : Int32) : UInt64 := i.toInt64.toUInt64
def sext16 (i : Int16) : UInt64 := i.toInt64.toUInt64

/-- 64-bit ALU. `none` = divide by zero. -/
def alu64 (op : AluOp) (a b : UInt64) : Option UInt64 :=
  match op with
  | .add => some (a + b) | .sub => some (a - b) | .mul => some (a * b)
  | .div => if b == 0 then none else some (a / b)
  | .mod => if b == 0 then none else some (a % b)
  | .or => some (a ||| b) | .and => some (a &&& b) | .xor => some (a ^^^ b)
  | .lsh => some (a <<< (b &&& 63)) | .rsh => some (a >>> (b &&& 63))
  | .arsh => some (a.toInt64 >>> (b &&& 63).toInt64).toUInt64
  | .mov => some b

/-- 32-bit ALU; result zero-extended (sBPF v0). -/
def alu32 (op : AluOp) (a b : UInt64) : Option UInt64 :=
  let x := a.toUInt32; let y := b.toUInt32
  let r : Option UInt32 := match op with
    | .add => some (x + y) | .sub => some (x - y) | .mul => some (x * y)
    | .div => if y == 0 then none else some (x / y)
    | .mod => if y == 0 then none else some (x % y)
    | .or => some (x ||| y) | .and => some (x &&& y) | .xor => some (x ^^^ y)
    | .lsh => some (x <<< (y &&& 31)) | .rsh => some (x >>> (y &&& 31))
    | .arsh => some (x.toInt32 >>> (y &&& 31).toInt32).toUInt32
    | .mov => some y
  r.map (·.toUInt64)

def jcc (c : JmpCond) (a b : UInt64) : Bool :=
  match c with
  | .eq => a == b | .ne => a != b | .gt => a > b | .ge => a ≥ b | .lt => a < b | .le => a ≤ b
  | .sgt => a.toInt64 > b.toInt64 | .sge => a.toInt64 ≥ b.toInt64
  | .slt => a.toInt64 < b.toInt64 | .sle => a.toInt64 ≤ b.toInt64
  | .set => (a &&& b) != 0

def garbage : UInt64 := 0xDEADBEEFCAFEF00D

/-- Copy `n` bytes inside VM memory. -/
def St.memcpy (s : St) (dst src n : UInt64) : St := Id.run do
  let mut st := s
  for i in [0:n.toNat] do
    st := { st with mem := st.mem.insert (dst + i.toUInt64) (s.readByte (src + i.toUInt64)) }
  return st

def doSyscall (s : St) (name : String) (pc : Nat) : Except Halt St := do
  let a1 := s.reg Reg.r1; let a2 := s.reg Reg.r2; let a3 := s.reg Reg.r3; let a4 := s.reg Reg.r4
  let chk (addr : UInt64) (n : UInt64) (w : Bool) : Except Halt Unit :=
    if n == 0 || s.mapped addr n.toNat w then pure () else throw (.accessViolation addr pc)
  let s' ← match name with
    | "abort" => throw .abort
    | "sol_log_" => do
        chk a1 a2 false
        let bytes := (List.range a2.toNat).map (fun i => s.readByte (a1 + i.toUInt64))
        pure { (s.set Reg.r0 0) with logs := s.logs.push (String.fromUTF8! ⟨bytes.toArray⟩) }
    | "sol_log_64_" => pure { (s.set Reg.r0 0) with
        logs := s.logs.push s!"log64 {a1} {a2} {a3} {a4} {s.reg Reg.r5}" }
    | "sol_log_compute_units_" => pure (s.set Reg.r0 0)
    | "sol_memcpy_" => do chk a1 a3 true; chk a2 a3 false; pure ((s.memcpy a1 a2 a3).set Reg.r0 0)
    | "sol_memset_" => do
        chk a1 a3 true
        let mut st := s
        for i in [0:a3.toNat] do
          st := { st with mem := st.mem.insert (a1 + i.toUInt64) a2.toUInt8 }
        pure (st.set Reg.r0 0)
    | "sol_memcmp_" => do
        chk a1 a3 false; chk a2 a3 false; chk a4 4 true
        let mut res : Int32 := 0
        for i in [0:a3.toNat] do
          if res == 0 then
            let x := s.readByte (a1 + i.toUInt64); let y := s.readByte (a2 + i.toUInt64)
            if x != y then res := Int32.ofNat x.toNat - Int32.ofNat y.toNat
        pure ((s.store a4 4 res.toUInt32.toUInt64).set Reg.r0 0)
    | other => throw (.unsupportedSyscall other)
  -- clobber caller-saved argument registers (stricter than the real VM)
  return [Reg.r1, Reg.r2, Reg.r3, Reg.r4, Reg.r5].foldl (fun st r => st.set r garbage) s'

/-- Precomputed label → pc table. -/
def labelTable (insns : Array Insn) : Std.HashMap String Nat := Id.run do
  let mut m : Std.HashMap String Nat := {}
  for h : i in [0:insns.size] do
    match insns[i] with
    | .label n => m := m.insert n i
    | _ => pure ()
  return m

partial def run (insns : Array Insn) (labels : Std.HashMap String Nat) (fuel : Nat)
    (pc : Nat) (s : St) : Halt × St :=
  if s.steps ≥ fuel then (.outOfFuel, s) else
  if h : pc < insns.size then
    let s := { s with steps := s.steps + 1 }
    let next (st : St) := run insns labels fuel (pc + 1) st
    let jump (lbl : String) (st : St) :=
      match labels.get? lbl with
      | some t => run insns labels fuel t st
      | none => (.badJump lbl, st)
    match insns[pc] with
    | .label _ => run insns labels fuel (pc + 1) { s with steps := s.steps - 1 }
    | .alu64Reg op d r =>
      match alu64 op (s.reg d) (s.reg r) with
      | some v => next (s.set d v) | none => (.divByZero pc, s)
    | .alu64Imm op d imm =>
      match alu64 op (s.reg d) (sext32 imm) with
      | some v => next (s.set d v) | none => (.divByZero pc, s)
    | .alu32Reg op d r =>
      match alu32 op (s.reg d) (s.reg r) with
      | some v => next (s.set d v) | none => (.divByZero pc, s)
    | .alu32Imm op d imm =>
      match alu32 op (s.reg d) imm.toUInt32.toUInt64 with
      | some v => next (s.set d v) | none => (.divByZero pc, s)
    | .neg64 d => next (s.set d (0 - s.reg d))
    | .lddw d v => next (s.set d v)
    | .lddwRodata d off => next (s.set d (rodataStart + off.toUInt64))
    | .ldx sz d r off =>
      let a := s.reg r + sext16 off
      if s.mapped a (sizeBytes sz) false then next (s.set d (s.load a (sizeBytes sz)))
      else (.accessViolation a pc, s)
    | .stx sz d r off =>
      let a := s.reg d + sext16 off
      if s.mapped a (sizeBytes sz) true then next (s.store a (sizeBytes sz) (s.reg r))
      else (.accessViolation a pc, s)
    | .stImm sz d off imm =>
      let a := s.reg d + sext16 off
      if s.mapped a (sizeBytes sz) true then next (s.store a (sizeBytes sz) (sext32 imm))
      else (.accessViolation a pc, s)
    | .ja t => jump t s
    | .jccReg c d r t => if jcc c (s.reg d) (s.reg r) then jump t s else next s
    | .jccImm c d imm t => if jcc c (s.reg d) (sext32 imm) then jump t s else next s
    | .callLocal t =>
      if s.frames.length + 1 ≥ maxFrames then (.callDepthExceeded, s) else
      let fr : Frame := { retPc := pc + 1, fp := s.reg Reg.r10,
                          saved := #[s.reg Reg.r6, s.reg Reg.r7, s.reg Reg.r8, s.reg Reg.r9] }
      let s := { s with frames := fr :: s.frames }
      jump t (s.set Reg.r10 (s.reg Reg.r10 + frameSize))
    | .callSyscall name =>
      match doSyscall s name pc with
      | .ok st => next st
      | .error h => (h, s)
    | .exit =>
      match s.frames with
      | [] => (.exit (s.reg Reg.r0), s)
      | fr :: rest =>
        let st := { s with frames := rest }
        let st := (((st.set Reg.r6 fr.saved[0]!).set Reg.r7 fr.saved[1]!).set Reg.r8 fr.saved[2]!).set
          Reg.r9 fr.saved[3]!
        run insns labels fuel fr.retPc (st.set Reg.r10 fr.fp)
  else (.badInsn pc, s)

/-- Execute a compiled program on an input buffer. Returns the halt reason and final state. -/
def execute (insns : Array Insn) (rodata : ByteArray) (input : ByteArray)
    (fuel : Nat := 1_400_000) : Halt × St := Id.run do
  let mut mem : Std.HashMap UInt64 UInt8 := {}
  for h : i in [0:input.size] do mem := mem.insert (inputStart + i.toUInt64) input[i]
  for h : i in [0:rodata.size] do mem := mem.insert (rodataStart + i.toUInt64) rodata[i]
  let regs := (Array.replicate 11 garbage)
    |>.set! 1 inputStart |>.set! 10 (stackStart + frameSize)
  let s : St := { regs, mem, inputLen := input.size.toUInt64, rodataLen := rodata.size.toUInt64,
                  frames := [], logs := #[], steps := 0 }
  run insns (labelTable insns) fuel 0 s

/-- Read back `n` bytes of the input region after execution (to inspect account mutations). -/
def St.inputBytes (s : St) (n : Nat) : ByteArray :=
  ⟨(List.range n).toArray.map (fun i => s.readByte (inputStart + i.toUInt64))⟩

end LemmaTest.Sbpf
