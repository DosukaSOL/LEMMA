/-
  LeanSVM.Compiler.RegAlloc
  Exact iterative CFG liveness analysis + loop-aware block layout + coalescing linear-scan
  register allocator targeting Solana sBPF (`r0..r9`, `r10`).
  - Places loop bodies immediately adjacent to loop headers.
  - Computes exact per-block `liveIn` / `liveOut` fixed-point dataflow sets.
  - Coalesces 2-address ALU dst with dying lhs and block params with incoming edge args!
  - Prioritizes callee-saved `r6..r9` for call/syscall-crossing live ranges.
  - Supports multi-parameter functions (`params[0..4]` prefer `r1..r5`).
  - Guarantees **0 spill bytes** whenever live values fit in registers.
-/
import LeanSVM.Compiler.IR
import LeanSVM.SBPF.ISA
import Std.Data.HashMap
import Std.Data.HashSet

namespace LeanSVM.Compiler

/-- Physical allocation location for a virtual register `VReg`. -/
inductive Loc where
  | reg (r : SBPF.Reg)
  | stack (off : Int16) -- negative offset from `r10`, e.g. `-8`, `-16`, ...
  | imm (val : UInt64)  -- rematerialized SSA constant (0 registers, 0 spills!)
  deriving Repr, BEq, Inhabited

/-- Result of register allocation for a function. -/
structure AllocResult where
  locs            : Std.HashMap VReg Loc
  orderedBlocks   : Array Block
  totalStackBytes : Nat -- aligned to 8 bytes (`stackAllocBytes + spillBytes`)
  spillCount      : Nat
  usesScratch     : Bool

/-- Order blocks in loop-friendly RPO so loop bodies stay next to their headers
    and cold error-exit blocks sink to the tail. -/
def orderBlocksRPO (f : Func) : Array Block := Id.run do
  let mut blkMap : Std.HashMap BlockId Block := {}
  for b in f.blocks do blkMap := blkMap.insert b.id b

  let isShortExit (bid : BlockId) : Bool :=
    match blkMap.get? bid with
    | some blk => blk.term.succs.isEmpty
    | none => false

  let reaches (start target : BlockId) : Bool := Id.run do
    let mut vis : Std.HashSet BlockId := {}
    let mut q : Array BlockId := #[start]
    vis := vis.insert start
    let mut qi := 0
    while qi < q.size do
      let cur := q[qi]!
      qi := qi + 1
      if let some blk := blkMap.get? cur then
        for s in blk.term.succs do
          if s == target then return true
          if !vis.contains s then
            vis := vis.insert s
            q := q.push s
    return false

  let mut visited : Std.HashSet BlockId := {}
  let mut postOrder : Array BlockId := #[]
  let mut stack : Array (BlockId × Bool) := #[(0, false)]
  while !stack.isEmpty do
    let (bid, expanded) := stack.back!
    stack := stack.pop
    if expanded then
      postOrder := postOrder.push bid
    else if !visited.contains bid then
      visited := visited.insert bid
      stack := stack.push (bid, true)
      if let some blk := blkMap.get? bid then
        let succs := blk.term.succs
        let orderedSuccs : Array BlockId :=
          if succs.size == 2 then
            let s0 := succs[0]!
            let s1 := succs[1]!
            let s0Loops := reaches s0 bid
            let s1Loops := reaches s1 bid
            if s1Loops && !s0Loops then #[s1, s0]
            else if s0Loops && !s1Loops then #[s0, s1]
            else if isShortExit s0 && !isShortExit s1 then #[s1, s0]
            else #[s0, s1]
          else succs
        for s in orderedSuccs do
          if !visited.contains s then
            stack := stack.push (s, false)

  let mut rpo : Array Block := Array.emptyWithCapacity postOrder.size
  let mut i := postOrder.size
  while i > 0 do
    i := i - 1
    if let some blk := blkMap.get? postOrder[i]! then
      rpo := rpo.push blk
  return rpo

private structure LiveInterval where
  vreg         : VReg
  startPos     : Nat
  endPos       : Nat
  useCount     : Nat
  crossesCall  : Bool
  preferReg?   : Option SBPF.Reg := none
  coalesceSrc? : Option VReg := none
  deriving Repr, Inhabited

/-- Compute exact per-block `liveIn` / `liveOut` dataflow sets + register coalescing hints. -/
private def computeIntervals (f : Func) (blocks : Array Block) : Array LiveInterval := Id.run do
  let mut blkUse : Std.HashMap BlockId (Std.HashSet VReg) := {}
  let mut blkDef : Std.HashMap BlockId (Std.HashSet VReg) := {}
  let mut useCounts : Std.HashMap VReg Nat := {}
  let mut coalesceHints : Std.HashMap VReg VReg := {}

  let bumpUse (m : Std.HashMap VReg Nat) (v : VReg) (w : Nat) : Std.HashMap VReg Nat :=
    m.insert v (m.getD v 0 + w)

  let mut blkMap : Std.HashMap BlockId Block := {}
  let mut blkIdx : Std.HashMap BlockId Nat := {}
  for idx in [0:blocks.size] do
    let blk := blocks[idx]!
    blkMap := blkMap.insert blk.id blk
    blkIdx := blkIdx.insert blk.id idx

  -- Detect natural loop blocks (any block between a back-edge target and its source in RPO)
  -- and weight their uses 10x so loop-carried variables always win physical registers!
  let mut inLoop : Std.HashSet BlockId := {}
  for idx in [0:blocks.size] do
    let blk := blocks[idx]!
    for s in blk.term.succs do
      if let some sIdx := blkIdx.get? s then
        if sIdx <= idx then
          for li in [sIdx : idx + 1] do
            inLoop := inLoop.insert blocks[li]!.id

  for blk in blocks do
    let w : Nat := if inLoop.contains blk.id then 10 else 1
    let mut uses : Std.HashSet VReg := {}
    let mut defs : Std.HashSet VReg := {}
    for bp in blk.params do defs := defs.insert bp
    if blk.id == 0 then
      for fp in f.params do defs := defs.insert fp
    for s in blk.stmts do
      for u in s.usedRegs do
        useCounts := bumpUse useCounts u w
        if !defs.contains u then uses := uses.insert u
      if let some d := s.defReg? then
        defs := defs.insert d
        -- Coalescing hint: 2-address ALU `dst = op lhs, ...` prefers `lhs`'s register!
        match s with
        | .binOp _ d l _ | .binImm _ d l _ | .mov d l | .neg64 d l =>
          coalesceHints := coalesceHints.insert d l
        | _ => pure ()
    for u in blk.term.usedRegs do
      useCounts := bumpUse useCounts u w
      if !defs.contains u then uses := uses.insert u
    -- Coalescing hint: block parameters prefer their incoming edge arguments!
    let recordEdgeHints (m : Std.HashMap VReg VReg) (tgt : BlockId) (args : Array VReg) :=
      match blkMap.get? tgt with
      | none => m
      | some tb => Id.run do
        let mut h := m
        for i in [0:min tb.params.size args.size] do
          let p := tb.params[i]!
          if !h.contains p then h := h.insert p args[i]!
        return h
    match blk.term with
    | .jmp t a => coalesceHints := recordEdgeHints coalesceHints t a
    | .br _ t ta e ea | .brCmp _ _ _ t ta e ea | .brCmpImm _ _ _ t ta e ea =>
      coalesceHints := recordEdgeHints (recordEdgeHints coalesceHints t ta) e ea
    | _ => pure ()
    blkUse := blkUse.insert blk.id uses
    blkDef := blkDef.insert blk.id defs

  let mut blkParams : Std.HashMap BlockId (Std.HashSet VReg) := {}
  for blk in blocks do
    let mut ps : Std.HashSet VReg := {}
    for p in blk.params do ps := ps.insert p
    blkParams := blkParams.insert blk.id ps

  let mut liveIn  : Std.HashMap BlockId (Std.HashSet VReg) := {}
  let mut liveOut : Std.HashMap BlockId (Std.HashSet VReg) := {}
  for blk in blocks do
    liveIn  := liveIn.insert blk.id (blkUse.getD blk.id {})
    liveOut := liveOut.insert blk.id {}

  let mut changed := true
  while changed do
    changed := false
    let mut bi := blocks.size
    while bi > 0 do
      bi := bi - 1
      let blk := blocks[bi]!
      let mut outSet := liveOut.getD blk.id {}
      for s in blk.term.succs do
        let sIn := liveIn.getD s {}
        let sPs := blkParams.getD s {}
        for v in sIn.toList do
          if !sPs.contains v && !outSet.contains v then
            outSet := outSet.insert v
            changed := true
      liveOut := liveOut.insert blk.id outSet

      let mut inSet := liveIn.getD blk.id {}
      let bDef := blkDef.getD blk.id {}
      for v in outSet.toList do
        if !bDef.contains v && !inSet.contains v then
          inSet := inSet.insert v
          changed := true
      liveIn := liveIn.insert blk.id inSet

  let mut firstDef : Std.HashMap VReg Nat := {}
  let mut lastUse  : Std.HashMap VReg Nat := {}
  let mut callPositions : Array Nat := #[]
  let mut pos : Nat := 1

  let recStart (m : Std.HashMap VReg Nat) (v : VReg) (p : Nat) : Std.HashMap VReg Nat :=
    match m.get? v with
    | some old => m.insert v (min old p)
    | none => m.insert v p

  let recEnd (m : Std.HashMap VReg Nat) (v : VReg) (p : Nat) : Std.HashMap VReg Nat :=
    match m.get? v with
    | some old => m.insert v (max old p)
    | none => m.insert v p

  for p in f.params do
    firstDef := recStart firstDef p 0
    lastUse  := recEnd lastUse p 0

  for blk in blocks do
    let bStart := pos
    for bp in blk.params do
      firstDef := recStart firstDef bp bStart
      lastUse  := recEnd lastUse bp bStart
    for v in (liveIn.getD blk.id {}).toList do
      firstDef := recStart firstDef v bStart
      lastUse  := recEnd lastUse v bStart
    pos := pos + 1
    for s in blk.stmts do
      for u in s.usedRegs do
        lastUse := recEnd lastUse u pos
      if s.isCallLike then
        callPositions := callPositions.push pos
      if let some d := s.defReg? then
        firstDef := recStart firstDef d pos
        lastUse  := recEnd lastUse d pos
      pos := pos + 1
    let bEnd := pos
    for u in blk.term.usedRegs do
      lastUse := recEnd lastUse u bEnd
    for v in (liveOut.getD blk.id {}).toList do
      lastUse := recEnd lastUse v bEnd
    pos := pos + 1

  let argRegs := #[SBPF.Reg.r1, SBPF.Reg.r2, SBPF.Reg.r3, SBPF.Reg.r4, SBPF.Reg.r5]
  let mut paramPref : Std.HashMap VReg SBPF.Reg := {}
  for idx in [0:min f.params.size 5] do
    paramPref := paramPref.insert f.params[idx]! argRegs[idx]!
  -- Hint shared `ret(p)` tail blocks and their incoming edge args to `r1` so error-return edges are 0-insn no-ops!
  let mut sharedRetBlks : Std.HashSet BlockId := {}
  for blk in blocks do
    if blk.id != 0 && blk.params.size == 1 && blk.stmts.isEmpty then
      match blk.term with
      | .ret rv =>
        if rv == blk.params[0]! then
          sharedRetBlks := sharedRetBlks.insert blk.id
          if !paramPref.contains rv then paramPref := paramPref.insert rv SBPF.Reg.r1
      | _ => pure ()
  if !sharedRetBlks.isEmpty then
    let hintRetEdge (m : Std.HashMap VReg SBPF.Reg) (tgt : BlockId) (args : Array VReg) :=
      if sharedRetBlks.contains tgt && args.size == 1 && !m.contains args[0]! then
        m.insert args[0]! SBPF.Reg.r1
      else m
    for blk in blocks do
      match blk.term with
      | .jmp t a => paramPref := hintRetEdge paramPref t a
      | .br _ t ta e ea | .brCmp _ _ _ t ta e ea | .brCmpImm _ _ _ t ta e ea =>
        paramPref := hintRetEdge (hintRetEdge paramPref t ta) e ea
      | _ => pure ()

  let mut intervals : Array LiveInterval := #[]
  for (v, dPos) in firstDef.toList do
    let uPos := max (lastUse.getD v dPos) (dPos + 1)
    let mut crosses := false
    for cp in callPositions do
      if dPos < cp && cp < uPos then
        crosses := true
        break
    let pref? : Option SBPF.Reg :=
      if crosses then none else paramPref.get? v
    intervals := intervals.push {
      vreg := v
      startPos := dPos
      endPos := uPos
      useCount := useCounts.getD v 1
      crossesCall := crosses
      preferReg? := pref?
      coalesceSrc? := coalesceHints.get? v
    }
  return intervals.qsort (fun a b =>
    if a.startPos != b.startPos then a.startPos < b.startPos else a.vreg < b.vreg)

/-- Run coalescing linear-scan allocation with caller-saved and callee-saved register pools. -/
private def runLinearScan (intervals : Array LiveInterval)
    (callerRegs calleeRegs : Array SBPF.Reg) (baseStackBytes : Nat) :
    Std.HashMap VReg Loc × Nat × Nat := Id.run do
  let mut locs : Std.HashMap VReg Loc := {}
  let mut active : Array (LiveInterval × SBPF.Reg) := #[]
  let mut activeSpills : Array (LiveInterval × Int16) := #[]
  -- Track `(slotOff, freedAtPos)` so a recycled slot is ONLY given to an interval with `startPos >= freedAtPos`!
  let mut freeSpillSlots : Array (Int16 × Nat) := #[]
  let mut nextSpillOff : Nat := ((baseStackBytes + 7) / 8) * 8
  let mut spillCount : Nat := 0

  let isRegFree (act : Array (LiveInterval × SBPF.Reg)) (r : SBPF.Reg) : Bool :=
    act.all (fun p => p.2 != r)

  for iv in intervals do
    -- Expire active register intervals
    active := active.filter (fun p => p.1.endPos > iv.startPos)
    -- Expire active spill intervals & record the exact position they became free
    let mut stillSpilled : Array (LiveInterval × Int16) := #[]
    for sp in activeSpills do
      if sp.1.endPos <= iv.startPos then
        freeSpillSlots := freeSpillSlots.push (sp.2, sp.1.endPos)
      else
        stillSpilled := stillSpilled.push sp
    activeSpills := stillSpilled

    let basePool : Array SBPF.Reg :=
      if iv.crossesCall then calleeRegs else callerRegs ++ calleeRegs

    let hintReg? : Option SBPF.Reg :=
      match iv.preferReg? with
      | some pr => some pr
      | none =>
        match iv.coalesceSrc? with
        | some srcV =>
          match locs.get? srcV with
          | some (.reg sr) => if basePool.contains sr then some sr else none
          | _ => none
        | none => none

    let candidates : Array SBPF.Reg :=
      match hintReg? with
      | some hr =>
        if basePool.contains hr then #[hr] ++ basePool.filter (· != hr) else basePool
      | none => basePool

    let mut chosen? : Option SBPF.Reg := none
    for r in candidates do
      if isRegFree active r then
        chosen? := some r
        break

    match chosen? with
    | some r =>
      locs := locs.insert iv.vreg (.reg r)
      active := active.push (iv, r)
    | none =>
      let mut bestIdx? : Option Nat := none
      let mut bestScore : Nat := iv.useCount
      let mut bestEnd : Nat := iv.endPos
      for idx in [0:active.size] do
        let (aiv, ar) := active[idx]!
        if !iv.crossesCall || calleeRegs.contains ar then
          if aiv.useCount < bestScore || (aiv.useCount == bestScore && aiv.endPos > bestEnd) then
            bestScore := aiv.useCount
            bestEnd := aiv.endPos
            bestIdx? := some idx

      -- Determine which interval is actually being spilled so we check its `startPos`!
      let targetStart : Nat :=
        match bestIdx? with
        | some bIdx => active[bIdx]!.1.startPos
        | none => iv.startPos

      -- Reuse a freed spill slot ONLY if it was freed at or before `targetStart`!
      let mut recycleIdx? : Option Nat := none
      for si in [0:freeSpillSlots.size] do
        if freeSpillSlots[si]!.2 <= targetStart then
          recycleIdx? := some si
          break

      let spillOff : Int16 ←
        match recycleIdx? with
        | some si =>
          let s := freeSpillSlots[si]!.1
          freeSpillSlots := freeSpillSlots.eraseIdx! si
          pure s
        | none =>
          nextSpillOff := nextSpillOff + 8
          pure (Int16.ofInt (-(nextSpillOff : Int)))

      spillCount := spillCount + 1
      let spillLoc := Loc.stack spillOff
      match bestIdx? with
      | some bIdx =>
        let (evicted, reg) := active[bIdx]!
        locs := locs.insert evicted.vreg spillLoc
        activeSpills := activeSpills.push (evicted, spillOff)
        locs := locs.insert iv.vreg (.reg reg)
        active := active.set! bIdx (iv, reg)
      | none =>
        locs := locs.insert iv.vreg spillLoc
        activeSpills := activeSpills.push (iv, spillOff)

  return (locs, nextSpillOff, spillCount)

/-- Collect all pure SSA `.constImm` definitions that can be rematerialized directly
    at use sites (zero register pressure, zero stack spills!). -/
private def collectRematConsts (f : Func) : Std.HashMap VReg UInt64 := Id.run do
  let mut defCount : Std.HashMap VReg Nat := {}
  let mut constVals : Std.HashMap VReg UInt64 := {}
  for p in f.params do
    defCount := defCount.insert p (defCount.getD p 0 + 1)
  for blk in f.blocks do
    for bp in blk.params do
      defCount := defCount.insert bp (defCount.getD bp 0 + 1)
    for s in blk.stmts do
      if let some d := s.defReg? then
        defCount := defCount.insert d (defCount.getD d 0 + 1)
      match s with
      | .constImm d v => constVals := constVals.insert d v
      | _ => pure ()
  let mut remat : Std.HashMap VReg UInt64 := {}
  for (v, val) in constVals.toList do
    if defCount.getD v 0 == 1 then
      remat := remat.insert v val
  return remat

/-- Allocate physical sBPF registers (and minimal stack spill slots only if required) for `f`. -/
def allocateRegisters (f : Func) : AllocResult :=
  let ordered := orderBlocksRPO f
  let rematConsts := collectRematConsts f
  let allIntervals := computeIntervals f ordered
  -- Exclude rematerialized constants from register/spill allocation!
  let intervals := allIntervals.filter (fun iv => !rematConsts.contains iv.vreg)
  let addImmLocs (m : Std.HashMap VReg Loc) : Std.HashMap VReg Loc :=
    rematConsts.fold (init := m) fun acc v val => acc.insert v (.imm val)
  let callee := #[SBPF.Reg.r6, SBPF.Reg.r7, SBPF.Reg.r8, SBPF.Reg.r9]
  let callerFull := #[SBPF.Reg.r1, SBPF.Reg.r2, SBPF.Reg.r3, SBPF.Reg.r4, SBPF.Reg.r5]
  let (locs1, stack1, spills1) := runLinearScan intervals callerFull callee f.stackAllocBytes
  if spills1 == 0 then
    { locs := addImmLocs locs1, orderedBlocks := ordered, totalStackBytes := stack1, spillCount := 0, usesScratch := false }
  else
    let callerSpill := #[SBPF.Reg.r1, SBPF.Reg.r2, SBPF.Reg.r3, SBPF.Reg.r4]
    let (locs2, stack2, spills2) := runLinearScan intervals callerSpill callee f.stackAllocBytes
    { locs := addImmLocs locs2, orderedBlocks := ordered, totalStackBytes := stack2, spillCount := spills2, usesScratch := true }

end LeanSVM.Compiler
