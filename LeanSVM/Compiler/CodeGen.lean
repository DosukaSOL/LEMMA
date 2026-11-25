/-
  LeanSVM.Compiler.CodeGen
  Direct SbfIR → Solana sBPF machine instruction generator.
  Handles:
  - Zero-overhead register-to-register execution when `spillCount == 0`
  - Immediate stores (`stdw`/`stw`/`sth`/`stb`) and direct `r10` stack accesses
  - Commutative 2-address operand swapping (turns 3-insn `mov+op+mov` into 1-insn `op`!)
  - Multi-parameter internal sBPF functions (`call local_fn`, `r1..r5 -> r0`)
  - Clobber-free spill reload/store via `(r0, r5)` when spills occur
  - Cycle-safe parallel edge moves for SSA block parameters
  - Fallthrough branch layout + final sBPF peephole pass
-/
import LeanSVM.Compiler.IR
import LeanSVM.Compiler.RegAlloc
import LeanSVM.SBPF.ISA
import LeanSVM.SBPF.Peephole

namespace LeanSVM.Compiler

open LeanSVM.SBPF

private def blkLabel (f : Func) (id : BlockId) : String :=
  if id == 0 then
    if f.isEntry then "entrypoint" else f.labelPrefix
  else
    s!"{f.labelPrefix}bb{id}"

private def getLoc (alloc : AllocResult) (v : VReg) : Loc :=
  alloc.locs.getD v (.reg Reg.r0)

/-- Load `v` into a physical register (no instruction if already in a register). -/
private def loadVReg (alloc : AllocResult) (v : VReg) (scratch : Reg) (out : Array Insn) :
    Reg × Array Insn :=
  match getLoc alloc v with
  | .reg r => (r, out)
  | .stack off => (scratch, out.push (.ldx .b8 scratch Reg.r10 off))

/-- Store result register `src` into `v`'s allocated location. -/
private def storeVReg (alloc : AllocResult) (v : VReg) (src : Reg) (out : Array Insn) : Array Insn :=
  match getLoc alloc v with
  | .reg r => if r == src then out else out.push (.alu64Reg .mov r src)
  | .stack off => out.push (.stx .b8 Reg.r10 src off)

/-- Emit a 64-bit constant into `dst` using the shortest sBPF encoding (`mov64`, `mov32`, or `lddw`). -/
private def emitConst64 (dst : Reg) (val : UInt64) (out : Array Insn) : Array Insn :=
  match fitsInt32 val with
  | some i32 => out.push (.alu64Imm .mov dst i32)
  | none =>
    match fitsUInt32 val with
    | some i32 => out.push (.alu32Imm .mov dst i32)
    | none => out.push (.lddw dst val)

/-- Emit cycle-safe parallel register/stack moves: `dsts[i] := srcs[i]`.
    `cycleTmp` (`r0`) breaks pure cycles; `memTmp` (`r5`, reserved whenever spills occur)
    handles stack-to-stack copies so `cycleTmp` is NEVER clobbered! -/
private def emitParallelLocMoves (moves : Array (Loc × Loc)) (cycleTmp : Reg) (memTmp : Reg := Reg.r5)
    (out : Array Insn) : Array Insn := Id.run do
  let mut pending := moves.filter (fun p => p.1 != p.2)
  let mut acc := out
  let mut guard := pending.size * 4 + 16
  while !pending.isEmpty && guard > 0 do
    guard := guard - 1
    let mut readyIdx? : Option Nat := none
    for i in [0:pending.size] do
      let dst := pending[i]!.1
      let readByOther := pending.any (fun p => p.2 == dst)
      if !readByOther then
        readyIdx? := some i
        break
    match readyIdx? with
    | some idx =>
      let (dst, src) := pending[idx]!
      pending := pending.eraseIdx! idx
      acc := match dst, src with
        | .reg dr, .reg sr     => acc.push (.alu64Reg .mov dr sr)
        | .reg dr, .stack soff => acc.push (.ldx .b8 dr Reg.r10 soff)
        | .stack doff, .reg sr => acc.push (.stx .b8 Reg.r10 sr doff)
        | .stack doff, .stack soff =>
          acc.push (.ldx .b8 memTmp Reg.r10 soff) |>.push (.stx .b8 Reg.r10 memTmp doff)
    | none =>
      let (dst, src) := pending[0]!
      pending := pending.eraseIdx! 0
      acc := match dst with
        | .reg dr => acc.push (.alu64Reg .mov cycleTmp dr)
        | .stack doff => acc.push (.ldx .b8 cycleTmp Reg.r10 doff)
      pending := pending.map (fun p => if p.2 == dst then (p.1, .reg cycleTmp) else p)
      acc := match dst, src with
        | .reg dr, .reg sr     => acc.push (.alu64Reg .mov dr sr)
        | .reg dr, .stack soff => acc.push (.ldx .b8 dr Reg.r10 soff)
        | .stack doff, .reg sr => acc.push (.stx .b8 Reg.r10 sr doff)
        | .stack doff, .stack soff =>
          acc.push (.ldx .b8 memTmp Reg.r10 soff) |>.push (.stx .b8 Reg.r10 memTmp doff)
  return acc

/-- Emit block-parameter edge moves from `args` into `targetBlock.params`. -/
private def emitEdgeMoves (alloc : AllocResult) (blkMap : Std.HashMap BlockId Block)
    (target : BlockId) (args : Array VReg) (out : Array Insn) : Array Insn :=
  match blkMap.get? target with
  | none => out
  | some tgtBlk =>
    let n := min tgtBlk.params.size args.size
    if n == 0 then out
    else Id.run do
      let mut moves : Array (Loc × Loc) := Array.emptyWithCapacity n
      for i in [0:n] do
        moves := moves.push (getLoc alloc tgtBlk.params[i]!, getLoc alloc args[i]!)
      return emitParallelLocMoves moves Reg.r0 Reg.r5 out

/-- Emit sBPF instructions for a single IR statement. -/
private def emitStmt (f : Func) (alloc : AllocResult) (stmt : Stmt) (cmpCounter : Nat) (out : Array Insn) :
    Array Insn × Nat :=
  match stmt with
  | .constImm dst val =>
    match getLoc alloc dst with
    | .reg dr => (emitConst64 dr val out, cmpCounter)
    | .stack off =>
      let o1 := emitConst64 Reg.r0 val out
      (o1.push (.stx .b8 Reg.r10 Reg.r0 off), cmpCounter)
  | .constRodata dst roOff =>
    match getLoc alloc dst with
    | .reg dr => (out.push (.lddwRodata dr roOff), cmpCounter)
    | .stack off =>
      (out.push (.lddwRodata Reg.r0 roOff) |>.push (.stx .b8 Reg.r10 Reg.r0 off), cmpCounter)
  | .mov dst src =>
    let (sr, o1) := loadVReg alloc src Reg.r0 out
    (storeVReg alloc dst sr o1, cmpCounter)
  | .neg64 dst src =>
    let (sr, o1) := loadVReg alloc src Reg.r0 out
    match getLoc alloc dst with
    | .reg dr =>
      let o2 := if dr == sr then o1 else o1.push (.alu64Reg .mov dr sr)
      (o2.push (.neg64 dr), cmpCounter)
    | .stack off =>
      let o2 := if sr == Reg.r0 then o1 else o1.push (.alu64Reg .mov Reg.r0 sr)
      (o2.push (.neg64 Reg.r0) |>.push (.stx .b8 Reg.r10 Reg.r0 off), cmpCounter)
  | .binImm op dst lhs imm =>
    let (lr, o1) := loadVReg alloc lhs Reg.r0 out
    let emitAlu (d : Reg) (acc : Array Insn) : Array Insn :=
      if op.is32 then acc.push (.alu32Imm op.toAluOp d imm)
      else acc.push (.alu64Imm op.toAluOp d imm)
    match getLoc alloc dst with
    | .reg dr =>
      let o2 := if dr == lr then o1 else o1.push (.alu64Reg .mov dr lr)
      (emitAlu dr o2, cmpCounter)
    | .stack off =>
      let o2 := if lr == Reg.r0 then o1 else o1.push (.alu64Reg .mov Reg.r0 lr)
      (emitAlu Reg.r0 o2 |>.push (.stx .b8 Reg.r10 Reg.r0 off), cmpCounter)
  | .binOp op dst lhs rhs =>
    let (lr, o1) := loadVReg alloc lhs Reg.r0 out
    let (rr, o2) := loadVReg alloc rhs Reg.r5 o1
    let emitAlu (d s : Reg) (acc : Array Insn) : Array Insn :=
      if op.is32 then acc.push (.alu32Reg op.toAluOp d s)
      else acc.push (.alu64Reg op.toAluOp d s)
    match getLoc alloc dst with
    | .reg dr =>
      if dr == lr then
        (emitAlu dr rr o2, cmpCounter)
      else if dr == rr then
        -- Commutative 2-address swap: `dst = lhs + dst` -> single `add64 dst, lhs`!
        if op.isCommutative then
          (emitAlu dr lr o2, cmpCounter)
        else
          let o3 := o2.push (.alu64Reg .mov Reg.r0 lr)
          let o4 := emitAlu Reg.r0 rr o3
          (o4.push (.alu64Reg .mov dr Reg.r0), cmpCounter)
      else
        let o3 := o2.push (.alu64Reg .mov dr lr)
        (emitAlu dr rr o3, cmpCounter)
    | .stack off =>
      let o3 := if lr == Reg.r0 then o2 else o2.push (.alu64Reg .mov Reg.r0 lr)
      let o4 := emitAlu Reg.r0 rr o3
      (o4.push (.stx .b8 Reg.r10 Reg.r0 off), cmpCounter)
  | .cmp op dst lhs rhs =>
    let (lr, o1) := loadVReg alloc lhs Reg.r0 out
    let (rr, o2) := loadVReg alloc rhs Reg.r5 o1
    let doneLbl := s!"{f.labelPrefix}_cmp_{cmpCounter}"
    let targetReg :=
      match getLoc alloc dst with
      | .reg dr => if dr != lr && dr != rr then dr else Reg.r0
      | .stack _ => Reg.r0
    let o3 := o2
      |>.push (.alu64Imm .mov targetReg 1)
      |>.push (.jccReg op.toJmpCond lr rr doneLbl)
      |>.push (.alu64Imm .mov targetReg 0)
      |>.push (.label doneLbl)
    (storeVReg alloc dst targetReg o3, cmpCounter + 1)
  | .load sz dst base off =>
    let (br, o1) := loadVReg alloc base Reg.r0 out
    match getLoc alloc dst with
    | .reg dr => (o1.push (.ldx sz dr br off), cmpCounter)
    | .stack soff =>
      (o1.push (.ldx sz Reg.r0 br off) |>.push (.stx .b8 Reg.r10 Reg.r0 soff), cmpCounter)
  | .store sz base off val =>
    let (br, o1) := loadVReg alloc base Reg.r0 out
    let (vr, o2) := loadVReg alloc val Reg.r5 o1
    (o2.push (.stx sz br vr off), cmpCounter)
  | .storeImm sz base off imm =>
    let (br, o1) := loadVReg alloc base Reg.r0 out
    (o1.push (.stImm sz br off imm), cmpCounter)
  | .loadStack sz dst off =>
    match getLoc alloc dst with
    | .reg dr => (out.push (.ldx sz dr Reg.r10 off), cmpCounter)
    | .stack soff =>
      (out.push (.ldx sz Reg.r0 Reg.r10 off) |>.push (.stx .b8 Reg.r10 Reg.r0 soff), cmpCounter)
  | .storeStack sz off val =>
    let (vr, o1) := loadVReg alloc val Reg.r0 out
    (o1.push (.stx sz Reg.r10 vr off), cmpCounter)
  | .storeStackImm sz off imm =>
    (out.push (.stImm sz Reg.r10 off imm), cmpCounter)
  | .stackAddr dst stackOff =>
    match getLoc alloc dst with
    | .reg dr =>
      (out.push (.alu64Reg .mov dr Reg.r10) |>.push (.alu64Imm .add dr (Int32.ofInt stackOff.toInt)), cmpCounter)
    | .stack soff =>
      (out.push (.alu64Reg .mov Reg.r0 Reg.r10)
        |>.push (.alu64Imm .add Reg.r0 (Int32.ofInt stackOff.toInt))
        |>.push (.stx .b8 Reg.r10 Reg.r0 soff), cmpCounter)
  | .syscall dst? sym args =>
    let argRegs := #[Reg.r1, Reg.r2, Reg.r3, Reg.r4, Reg.r5]
    let n := min args.size 5
    let moves : Array (Loc × Loc) := Id.run do
      let mut ms : Array (Loc × Loc) := Array.emptyWithCapacity n
      for i in [0:n] do
        ms := ms.push (.reg argRegs[i]!, getLoc alloc args[i]!)
      return ms
    let o1 := emitParallelLocMoves moves Reg.r0 Reg.r5 out
    let o2 := o1.push (.callSyscall sym)
    let o3 :=
      match dst? with
      | some d => storeVReg alloc d Reg.r0 o2
      | none => o2
    (o3, cmpCounter)
  | .call dst? fnLabel args =>
    let argRegs := #[Reg.r1, Reg.r2, Reg.r3, Reg.r4, Reg.r5]
    let n := min args.size 5
    let moves : Array (Loc × Loc) := Id.run do
      let mut ms : Array (Loc × Loc) := Array.emptyWithCapacity n
      for i in [0:n] do
        ms := ms.push (.reg argRegs[i]!, getLoc alloc args[i]!)
      return ms
    let o1 := emitParallelLocMoves moves Reg.r0 Reg.r5 out
    let o2 := o1.push (.callLocal fnLabel)
    let o3 :=
      match dst? with
      | some d => storeVReg alloc d Reg.r0 o2
      | none => o2
    (o3, cmpCounter)

/-- Generate optimized sBPF machine instructions for a single SSA `Func`. -/
def generateFuncCode (f : Func) : Array Insn × AllocResult := Id.run do
  let alloc := allocateRegisters f
  let blocks := alloc.orderedBlocks
  let mut blkMap : Std.HashMap BlockId Block := {}
  for b in blocks do blkMap := blkMap.insert b.id b

  let mut out : Array Insn := #[]
  let mut auxCounter : Nat := 0

  for bi in [0:blocks.size] do
    let blk := blocks[bi]!
    let nextBlkId? : Option BlockId :=
      if bi + 1 < blocks.size then some blocks[bi + 1]!.id else none

    out := out.push (.label (blkLabel f blk.id))

    -- Entry block: move incoming `r1..r5` into allocated parameter locations in parallel!
    if blk.id == 0 && !f.params.isEmpty then
      let argRegs := #[Reg.r1, Reg.r2, Reg.r3, Reg.r4, Reg.r5]
      let n := min f.params.size 5
      let mut pMoves : Array (Loc × Loc) := Array.emptyWithCapacity n
      for i in [0:n] do
        pMoves := pMoves.push (getLoc alloc f.params[i]!, .reg argRegs[i]!)
      out := emitParallelLocMoves pMoves Reg.r0 Reg.r5 out

    for stmt in blk.stmts do
      let (o', c') := emitStmt f alloc stmt auxCounter out
      out := o'
      auxCounter := c'

    match blk.term with
    | .ret v =>
      let (vr, o1) := loadVReg alloc v Reg.r0 out
      let o2 := if vr == Reg.r0 then o1 else o1.push (.alu64Reg .mov Reg.r0 vr)
      out := o2.push .exit
    | .unreach =>
      out := out.push (.alu64Imm .mov Reg.r0 1) |>.push .exit
    | .jmp tgt args =>
      out := emitEdgeMoves alloc blkMap tgt args out
      if nextBlkId? != some tgt then
        out := out.push (.ja (blkLabel f tgt))
    | .br cond tBlk tArgs eBlk eArgs =>
      let (cr, o1) := loadVReg alloc cond Reg.r0 out
      if tArgs.isEmpty && eArgs.isEmpty then
        if nextBlkId? == some tBlk then
          out := o1.push (.jccImm .eq cr 0 (blkLabel f eBlk))
        else if nextBlkId? == some eBlk then
          out := o1.push (.jccImm .ne cr 0 (blkLabel f tBlk))
        else
          out := o1.push (.jccImm .ne cr 0 (blkLabel f tBlk)) |>.push (.ja (blkLabel f eBlk))
      else
        let elseEdge := s!"{f.labelPrefix}_e{auxCounter}"
        auxCounter := auxCounter + 1
        out := o1.push (.jccImm .eq cr 0 elseEdge)
        out := emitEdgeMoves alloc blkMap tBlk tArgs out
        out := out.push (.ja (blkLabel f tBlk))
        out := out.push (.label elseEdge)
        out := emitEdgeMoves alloc blkMap eBlk eArgs out
        if nextBlkId? != some eBlk then
          out := out.push (.ja (blkLabel f eBlk))
    | .brCmp op l r tBlk tArgs eBlk eArgs =>
      let (lr, o1) := loadVReg alloc l Reg.r0 out
      let (rr, o2) := loadVReg alloc r Reg.r5 o1
      if tArgs.isEmpty && eArgs.isEmpty then
        if nextBlkId? == some tBlk then
          out := o2.push (.jccReg op.invert.toJmpCond lr rr (blkLabel f eBlk))
        else if nextBlkId? == some eBlk then
          out := o2.push (.jccReg op.toJmpCond lr rr (blkLabel f tBlk))
        else
          out := o2.push (.jccReg op.toJmpCond lr rr (blkLabel f tBlk)) |>.push (.ja (blkLabel f eBlk))
      else if tArgs.isEmpty && nextBlkId? != some tBlk then
        out := o2.push (.jccReg op.toJmpCond lr rr (blkLabel f tBlk))
        out := emitEdgeMoves alloc blkMap eBlk eArgs out
        if nextBlkId? != some eBlk then
          out := out.push (.ja (blkLabel f eBlk))
      else if eArgs.isEmpty && nextBlkId? != some eBlk then
        out := o2.push (.jccReg op.invert.toJmpCond lr rr (blkLabel f eBlk))
        out := emitEdgeMoves alloc blkMap tBlk tArgs out
        if nextBlkId? != some tBlk then
          out := out.push (.ja (blkLabel f tBlk))
      else
        let elseEdge := s!"{f.labelPrefix}_e{auxCounter}"
        auxCounter := auxCounter + 1
        out := o2.push (.jccReg op.invert.toJmpCond lr rr elseEdge)
        out := emitEdgeMoves alloc blkMap tBlk tArgs out
        out := out.push (.ja (blkLabel f tBlk))
        out := out.push (.label elseEdge)
        out := emitEdgeMoves alloc blkMap eBlk eArgs out
        if nextBlkId? != some eBlk then
          out := out.push (.ja (blkLabel f eBlk))
    | .brCmpImm op l imm tBlk tArgs eBlk eArgs =>
      let (lr, o1) := loadVReg alloc l Reg.r0 out
      if tArgs.isEmpty && eArgs.isEmpty then
        if nextBlkId? == some tBlk then
          out := o1.push (.jccImm op.invert.toJmpCond lr imm (blkLabel f eBlk))
        else if nextBlkId? == some eBlk then
          out := o1.push (.jccImm op.toJmpCond lr imm (blkLabel f tBlk))
        else
          out := o1.push (.jccImm op.toJmpCond lr imm (blkLabel f tBlk)) |>.push (.ja (blkLabel f eBlk))
      else if tArgs.isEmpty && nextBlkId? != some tBlk then
        out := o1.push (.jccImm op.toJmpCond lr imm (blkLabel f tBlk))
        out := emitEdgeMoves alloc blkMap eBlk eArgs out
        if nextBlkId? != some eBlk then
          out := out.push (.ja (blkLabel f eBlk))
      else if eArgs.isEmpty && nextBlkId? != some eBlk then
        out := o1.push (.jccImm op.invert.toJmpCond lr imm (blkLabel f eBlk))
        out := emitEdgeMoves alloc blkMap tBlk tArgs out
        if nextBlkId? != some tBlk then
          out := out.push (.ja (blkLabel f tBlk))
      else
        let elseEdge := s!"{f.labelPrefix}_e{auxCounter}"
        auxCounter := auxCounter + 1
        out := o1.push (.jccImm op.invert.toJmpCond lr imm elseEdge)
        out := emitEdgeMoves alloc blkMap tBlk tArgs out
        out := out.push (.ja (blkLabel f tBlk))
        out := out.push (.label elseEdge)
        out := emitEdgeMoves alloc blkMap eBlk eArgs out
        if nextBlkId? != some eBlk then
          out := out.push (.ja (blkLabel f eBlk))

  return (out, alloc)

/-- Backwards-compatible single-function wrapper. -/
def generateCode (f : Func) : Array Insn × AllocResult :=
  let (insns, alloc) := generateFuncCode f
  (peepholeOptimize insns, alloc)

/-- Generate and peephole-optimize a complete multi-function `Program` (`entry` + outlined helpers). -/
def generateProgramCode (prog : Program) : Array Insn × AllocResult × Nat := Id.run do
  let (entryInsns, entryAlloc) := generateFuncCode prog.entry
  let mut allInsns := entryInsns
  let mut maxStack := entryAlloc.totalStackBytes
  let mut totalSpills := entryAlloc.spillCount
  for h in prog.helpers do
    let (hInsns, hAlloc) := generateFuncCode h
    allInsns := allInsns ++ hInsns
    maxStack := max maxStack hAlloc.totalStackBytes
    totalSpills := totalSpills + hAlloc.spillCount
  let optimized := peepholeOptimize allInsns
  return (optimized, { entryAlloc with totalStackBytes := maxStack, spillCount := totalSpills }, prog.helpers.size)

end LeanSVM.Compiler
