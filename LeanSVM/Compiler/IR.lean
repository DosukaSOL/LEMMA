/-
  LeanSVM.Compiler.IR
  Minimal, register-oriented SSA / block-parameter Intermediate Representation (`SbfIR`).
  Every value is an unboxed 64-bit scalar (`VReg`); zero heap allocations exist in the IR.
  Supports direct `r10` stack accesses, immediate stores (`stImm`), and internal sBPF `call`s.
-/
import LeanSVM.SBPF.ISA

namespace LeanSVM.Compiler

abbrev VReg := Nat
abbrev BlockId := Nat

inductive BinOp where
  | add64 | sub64 | mul64 | div64 | mod64 | or64 | and64 | xor64 | lsh64 | rsh64 | arsh64
  | add32 | sub32 | mul32 | div32 | mod32 | or32 | and32 | xor32 | lsh32 | rsh32
  deriving Repr, BEq, DecidableEq, Inhabited

inductive CmpOp where
  | eq | ne | ult | ule | ugt | uge | slt | sle | sgt | sge
  deriving Repr, BEq, DecidableEq, Inhabited

namespace CmpOp
  def toJmpCond : CmpOp → SBPF.JmpCond
    | .eq  => .eq
    | .ne  => .ne
    | .ult => .lt
    | .ule => .le
    | .ugt => .gt
    | .uge => .ge
    | .slt => .slt
    | .sle => .sle
    | .sgt => .sgt
    | .sge => .sge

  def invert : CmpOp → CmpOp
    | .eq  => .ne
    | .ne  => .eq
    | .ult => .uge
    | .ule => .ugt
    | .ugt => .ule
    | .uge => .ult
    | .slt => .sge
    | .sle => .sgt
    | .sgt => .sle
    | .sge => .slt

  /-- Swap operands: `a op b` ↔ `b (flip op) a`. -/
  def flip : CmpOp → CmpOp
    | .eq  => .eq
    | .ne  => .ne
    | .ult => .ugt
    | .ule => .uge
    | .ugt => .ult
    | .uge => .ule
    | .slt => .sgt
    | .sle => .sge
    | .sgt => .slt
    | .sge => .sle

  def evalU64 (op : CmpOp) (a b : UInt64) : Bool :=
    match op with
    | .eq  => a == b
    | .ne  => a != b
    | .ult => a < b
    | .ule => a <= b
    | .ugt => a > b
    | .uge => a >= b
    | .slt => a.toInt64 < b.toInt64
    | .sle => a.toInt64 <= b.toInt64
    | .sgt => a.toInt64 > b.toInt64
    | .sge => a.toInt64 >= b.toInt64
end CmpOp

namespace BinOp
  def is32 : BinOp → Bool
    | .add32 | .sub32 | .mul32 | .div32 | .mod32
    | .or32  | .and32 | .xor32 | .lsh32 | .rsh32 => true
    | _ => false

  def isCommutative : BinOp → Bool
    | .add64 | .mul64 | .or64 | .and64 | .xor64
    | .add32 | .mul32 | .or32 | .and32 | .xor32 => true
    | _ => false

  def toAluOp : BinOp → SBPF.AluOp
    | .add64 | .add32 => .add
    | .sub64 | .sub32 => .sub
    | .mul64 | .mul32 => .mul
    | .div64 | .div32 => .div
    | .mod64 | .mod32 => .mod
    | .or64  | .or32  => .or
    | .and64 | .and32 => .and
    | .xor64 | .xor32 => .xor
    | .lsh64 | .lsh32 => .lsh
    | .rsh64 | .rsh32 => .rsh
    | .arsh64         => .arsh

  def evalConst (op : BinOp) (a b : UInt64) : Option UInt64 :=
    match op with
    | .add64  => some (a + b)
    | .sub64  => some (a - b)
    | .mul64  => some (a * b)
    | .div64  => if b == 0 then none else some (a / b)
    | .mod64  => if b == 0 then none else some (a % b)
    | .or64   => some (a ||| b)
    | .and64  => some (a &&& b)
    | .xor64  => some (a ^^^ b)
    | .lsh64  => some (a <<< (b &&& 63))
    | .rsh64  => some (a >>> (b &&& 63))
    | .arsh64 => some (a.toInt64 >>> (b &&& 63).toInt64).toUInt64
    | .add32  => some (a.toUInt32 + b.toUInt32).toUInt64
    | .sub32  => some (a.toUInt32 - b.toUInt32).toUInt64
    | .mul32  => some (a.toUInt32 * b.toUInt32).toUInt64
    | .div32  => if b.toUInt32 == 0 then none else some (a.toUInt32 / b.toUInt32).toUInt64
    | .mod32  => if b.toUInt32 == 0 then none else some (a.toUInt32 % b.toUInt32).toUInt64
    | .or32   => some (a.toUInt32 ||| b.toUInt32).toUInt64
    | .and32  => some (a.toUInt32 &&& b.toUInt32).toUInt64
    | .xor32  => some (a.toUInt32 ^^^ b.toUInt32).toUInt64
    | .lsh32  => some (a.toUInt32 <<< (b.toUInt32 &&& 31)).toUInt64
    | .rsh32  => some (a.toUInt32 >>> (b.toUInt32 &&& 31)).toUInt64
end BinOp

/-- SSA IR statement. -/
inductive Stmt where
  | constImm (dst : VReg) (val : UInt64)
  | constRodata (dst : VReg) (roOff : UInt32)
  | mov (dst src : VReg)
  | binOp (op : BinOp) (dst lhs rhs : VReg)
  | binImm (op : BinOp) (dst lhs : VReg) (imm : Int32)
  | neg64 (dst src : VReg)
  | cmp (op : CmpOp) (dst lhs rhs : VReg)
  | load (sz : SBPF.MemSize) (dst base : VReg) (off : Int16)
  | store (sz : SBPF.MemSize) (base : VReg) (off : Int16) (val : VReg)
  | storeImm (sz : SBPF.MemSize) (base : VReg) (off : Int16) (imm : Int32)
  | loadStack (sz : SBPF.MemSize) (dst : VReg) (stackOff : Int16)
  | storeStack (sz : SBPF.MemSize) (stackOff : Int16) (val : VReg)
  | storeStackImm (sz : SBPF.MemSize) (stackOff : Int16) (imm : Int32)
  | stackAddr (dst : VReg) (stackOff : Int16)
  | syscall (dst? : Option VReg) (sym : String) (args : Array VReg)
  | call (dst? : Option VReg) (fnLabel : String) (args : Array VReg)
  deriving Repr, BEq, Inhabited

/-- SSA basic block terminator (supports block parameters for zero-overhead SSA). -/
inductive Term where
  | jmp (target : BlockId) (args : Array VReg)
  | br (cond : VReg) (tBlk : BlockId) (tArgs : Array VReg) (eBlk : BlockId) (eArgs : Array VReg)
  | brCmp (op : CmpOp) (lhs rhs : VReg) (tBlk : BlockId) (tArgs : Array VReg) (eBlk : BlockId) (eArgs : Array VReg)
  | brCmpImm (op : CmpOp) (lhs : VReg) (imm : Int32) (tBlk : BlockId) (tArgs : Array VReg) (eBlk : BlockId) (eArgs : Array VReg)
  | ret (val : VReg)
  | unreach
  deriving Repr, BEq, Inhabited

structure Block where
  id     : BlockId
  params : Array VReg := #[]
  stmts  : Array Stmt := #[]
  term   : Term := .unreach
  deriving Repr, Inhabited

structure Func where
  name            : String
  labelPrefix     : String := ""
  isEntry         : Bool := true
  params          : Array VReg
  blocks          : Array Block
  stackAllocBytes : Nat := 0
  nextVReg        : Nat := 0
  deriving Repr, Inhabited

/-- Deduplicated `.rodata` string/constant pool. -/
structure RodataPool where
  bytes   : ByteArray := ByteArray.empty
  entries : List (ByteArray × UInt32) := []

def RodataPool.internBytes (pool : RodataPool) (data : ByteArray) : RodataPool × UInt32 :=
  match pool.entries.find? (fun p => p.1 == data) with
  | some (_, off) => (pool, off)
  | none =>
    let off := pool.bytes.size.toUInt32
    let bytes' := pool.bytes ++ data
    ({ bytes := bytes', entries := (data, off) :: pool.entries }, off)

def RodataPool.internString (pool : RodataPool) (s : String) : RodataPool × UInt32 × UInt64 :=
  let utf8 := s.toUTF8
  let (pool', off) := pool.internBytes utf8
  (pool', off, utf8.size.toUInt64)

structure Program where
  entry   : Func
  helpers : Array Func := #[]
  rodata  : ByteArray

/-! ### Statement / Terminator Queries -/

def Stmt.defReg? : Stmt → Option VReg
  | .constImm d _          => some d
  | .constRodata d _       => some d
  | .mov d _               => some d
  | .binOp _ d _ _         => some d
  | .binImm _ d _ _        => some d
  | .neg64 d _             => some d
  | .cmp _ d _ _           => some d
  | .load _ d _ _          => some d
  | .loadStack _ d _       => some d
  | .store ..              => none
  | .storeImm ..           => none
  | .storeStack ..         => none
  | .storeStackImm ..      => none
  | .stackAddr d _         => some d
  | .syscall d? _ _        => d?
  | .call d? _ _           => d?

def Stmt.hasSideEffect : Stmt → Bool
  | .store ..         => true
  | .storeImm ..      => true
  | .storeStack ..    => true
  | .storeStackImm .. => true
  | .syscall ..       => true
  | .call ..          => true
  | _                 => false

def Stmt.isCallLike : Stmt → Bool
  | .syscall .. | .call .. => true
  | _ => false

def Stmt.usedRegs : Stmt → Array VReg
  | .constImm _ _          => #[]
  | .constRodata _ _       => #[]
  | .mov _ s               => #[s]
  | .binOp _ _ l r         => #[l, r]
  | .binImm _ _ l _        => #[l]
  | .neg64 _ s             => #[s]
  | .cmp _ _ l r           => #[l, r]
  | .load _ _ b _          => #[b]
  | .store _ b _ v         => #[b, v]
  | .storeImm _ b _ _      => #[b]
  | .loadStack _ _ _       => #[]
  | .storeStack _ _ v      => #[v]
  | .storeStackImm _ _ _   => #[]
  | .stackAddr _ _         => #[]
  | .syscall _ _ args      => args
  | .call _ _ args         => args

def Term.usedRegs : Term → Array VReg
  | .jmp _ args                     => args
  | .br c _ ta _ ea                 => #[c] ++ ta ++ ea
  | .brCmp _ l r _ ta _ ea          => #[l, r] ++ ta ++ ea
  | .brCmpImm _ l _ _ ta _ ea       => #[l] ++ ta ++ ea
  | .ret v                          => #[v]
  | .unreach                        => #[]

def Term.succs : Term → Array BlockId
  | .jmp t _               => #[t]
  | .br _ t _ e _          => #[t, e]
  | .brCmp _ _ _ t _ e _   => #[t, e]
  | .brCmpImm _ _ _ t _ e _=> #[t, e]
  | .ret _                 => #[]
  | .unreach               => #[]

/-! ### IR Pretty Printer (`--dump-ir`) -/

private def fmtVRegs (rs : Array VReg) : String :=
  String.intercalate ", " (rs.toList.map fun r => s!"v{r}")

def formatStmt : Stmt → String
  | .constImm d v          => s!"  v{d} = const {v} (0x{String.ofList (Nat.toDigits 16 v.toNat)})"
  | .constRodata d off     => s!"  v{d} = &.rodata+{off}"
  | .mov d s               => s!"  v{d} = v{s}"
  | .binOp op d l r        => s!"  v{d} = {repr op} v{l}, v{r}"
  | .binImm op d l imm     => s!"  v{d} = {repr op} v{l}, {imm}"
  | .neg64 d s             => s!"  v{d} = neg64 v{s}"
  | .cmp op d l r          => s!"  v{d} = cmp.{repr op} v{l}, v{r}"
  | .load sz d b off       => s!"  v{d} = load.{repr sz} [v{b} + {off}]"
  | .store sz b off v      => s!"  store.{repr sz} [v{b} + {off}], v{v}"
  | .storeImm sz b off imm => s!"  storeImm.{repr sz} [v{b} + {off}], {imm}"
  | .loadStack sz d off    => s!"  v{d} = load.{repr sz} [r10 + {off}]"
  | .storeStack sz off v   => s!"  store.{repr sz} [r10 + {off}], v{v}"
  | .storeStackImm sz off i=> s!"  storeImm.{repr sz} [r10 + {off}], {i}"
  | .stackAddr d off       => s!"  v{d} = r10 + {off}"
  | .syscall none s a      => s!"  syscall {s}({fmtVRegs a})"
  | .syscall (some d) s a  => s!"  v{d} = syscall {s}({fmtVRegs a})"
  | .call none s a         => s!"  call {s}({fmtVRegs a})"
  | .call (some d) s a     => s!"  v{d} = call {s}({fmtVRegs a})"

def formatTerm : Term → String
  | .jmp t a              => s!"  jmp bb{t}({fmtVRegs a})"
  | .br c t ta e ea       => s!"  br v{c}, bb{t}({fmtVRegs ta}), bb{e}({fmtVRegs ea})"
  | .brCmp op l r t ta e ea =>
    s!"  br.{repr op} v{l}, v{r}, bb{t}({fmtVRegs ta}), bb{e}({fmtVRegs ea})"
  | .brCmpImm op l imm t ta e ea =>
    s!"  br.{repr op} v{l}, {imm}, bb{t}({fmtVRegs ta}), bb{e}({fmtVRegs ea})"
  | .ret v                => s!"  ret v{v}"
  | .unreach              => "  unreachable"

def formatFunc (f : Func) : String :=
  let hdr := s!"fn {f.name}({fmtVRegs f.params}) [stack={f.stackAllocBytes}B]:"
  let bStrs := f.blocks.toList.map fun b =>
    let bHdr := s!"bb{b.id}({fmtVRegs b.params}):"
    let sStrs := b.stmts.toList.map formatStmt
    String.intercalate "\n" ([bHdr] ++ sStrs ++ [formatTerm b.term])
  String.intercalate "\n" (hdr :: bStrs)

end LeanSVM.Compiler
