/-
  LeanSVM.Compiler.Optimize
  High-impact SSA IR optimizer for Solana sBPF (designed to rival/beat hand-rolled sBPF):
  1. Copy propagation & constant block-parameter propagation
  2. Constant folding & power-of-2 strength reduction (`mul/div/mod` -> `lsh/rsh/and`)
  3. Immediate operand folding (`binOp` -> `binImm`, `store` -> `storeImm`)
  4. Address-offset folding (`v = base + k; load/store [v + off]` -> `load/store [base + (k + off)]`)
  5. Direct `r10` stack folding (`v = r10 + sOff; load/store [v + off]` -> `loadStack/storeStack/storeStackImm`)
  6. Compare-and-branch fusion & operand flipping (`1 <= r` -> `r >= 1`)
  7. Local CSE (deduplicates repeated pure ALU/address computations within blocks)
  8. Dead Code & Dead Block-Parameter Elimination (DCE)
  9. Tail Merging (deduplicates identical error-exit blocks -> slashes `.so` binary size!)
  10. Unreachable block & forwarding-trampoline pruning
-/
import LeanSVM.Compiler.IR
import LeanSVM.SBPF.Peephole
import Std.Data.HashMap
import Std.Data.HashSet

namespace LeanSVM.Compiler

private def log2IfPow2 (v : UInt64) : Option Nat :=
  if v == 0 || (v &&& (v - 1)) != 0 then none
  else
    let rec go (x : UInt64) (k : Nat) (fuel : Nat) : Nat :=
      match fuel with
      | 0 => k
      | n + 1 => if x <= 1 then k else go (x >>> 1) (k + 1) n
    some (go v 0 64)

private def fitsInt16 (x : Int) : Option Int16 :=
  if x >= -32768 && x <= 32767 then some (Int16.ofInt x) else none

private def fitsInt32Int (x : Int) : Option Int32 :=
  if x >= -2147483648 && x <= 2147483647 then some (Int32.ofInt x) else none

private def fitsInt32U64 (v : UInt64) : Option Int32 :=
  SBPF.fitsInt32 v

private def resolveAlias (aliasMap : Std.HashMap VReg VReg) (v : VReg) : VReg := Id.run do
  let mut cur := v
  for _ in [0:16] do
    match aliasMap.get? cur with
    | some nxt => if nxt == cur then break else cur := nxt
    | none => break
  return cur

/-- Substitute register aliases in a statement. -/
private def substStmt (am : Std.HashMap VReg VReg) : Stmt → Stmt
  | .mov d s               => .mov d (resolveAlias am s)
  | .binOp op d l r        => .binOp op d (resolveAlias am l) (resolveAlias am r)
  | .binImm op d l imm     => .binImm op d (resolveAlias am l) imm
  | .neg64 d s             => .neg64 d (resolveAlias am s)
  | .cmp op d l r          => .cmp op d (resolveAlias am l) (resolveAlias am r)
  | .load sz d b off       => .load sz d (resolveAlias am b) off
  | .store sz b off v      => .store sz (resolveAlias am b) off (resolveAlias am v)
  | .storeImm sz b off imm => .storeImm sz (resolveAlias am b) off imm
  | .storeStack sz off v   => .storeStack sz off (resolveAlias am v)
  | .syscall d? s args     => .syscall d? s (args.map (resolveAlias am))
  | .call d? s args        => .call d? s (args.map (resolveAlias am))
  | s                      => s

/-- Substitute register aliases in a terminator. -/
private def substTerm (am : Std.HashMap VReg VReg) : Term → Term
  | .jmp t a                     => .jmp t (a.map (resolveAlias am))
  | .br c t ta e ea              => .br (resolveAlias am c) t (ta.map (resolveAlias am)) e (ea.map (resolveAlias am))
  | .brCmp op l r t ta e ea      => .brCmp op (resolveAlias am l) (resolveAlias am r) t (ta.map (resolveAlias am)) e (ea.map (resolveAlias am))
  | .brCmpImm op l imm t ta e ea => .brCmpImm op (resolveAlias am l) imm t (ta.map (resolveAlias am)) e (ea.map (resolveAlias am))
  | .ret v                       => .ret (resolveAlias am v)
  | .unreach                     => .unreach

/-- Forward pass: copy propagation, constant folding, strength reduction, address-offset &
    direct `r10` stack folding, `storeImm` folding, local CSE, and compare-branch fusion. -/
private def forwardOptPass (f : Func) : Func × Bool := Id.run do
  let mut consts    : Std.HashMap VReg UInt64 := {}
  let mut aliases   : Std.HashMap VReg VReg := {}
  let mut addOffs   : Std.HashMap VReg (VReg × Int) := {} -- v = base + offset
  let mut stackOffs : Std.HashMap VReg Int := {}          -- v = r10 + offset
  let mut cmpDefs   : Std.HashMap VReg (CmpOp × VReg × VReg) := {}
  let mut changed   := false

  -- Pre-scan `constImm` and propagate constant block parameters across incoming edges
  let mut incomingArgs : Std.HashMap BlockId (Array (Array VReg)) := {}
  let addIncoming (m : Std.HashMap BlockId (Array (Array VReg))) (tgt : BlockId) (args : Array VReg) :=
    if args.isEmpty then m else m.insert tgt ((m.getD tgt #[]).push args)
  for blk in f.blocks do
    for s in blk.stmts do
      match s with
      | .constImm d v => consts := consts.insert d v
      | _ => pure ()
    match blk.term with
    | .jmp t a => incomingArgs := addIncoming incomingArgs t a
    | .br _ t ta e ea | .brCmp _ _ _ t ta e ea | .brCmpImm _ _ _ t ta e ea =>
      incomingArgs := addIncoming (addIncoming incomingArgs t ta) e ea
    | _ => pure ()

  for blk in f.blocks do
    if !blk.params.isEmpty then
      if let some edges := incomingArgs.get? blk.id then
        if !edges.isEmpty then
          for k in [0:blk.params.size] do
            let mut common? : Option UInt64 := none
            let mut allSame := true
            for edge in edges do
              if k < edge.size then
                match consts.get? edge[k]! with
                | some cv =>
                  match common? with
                  | none => common? := some cv
                  | some prev => if prev != cv then allSame := false
                | none => allSame := false
              else allSame := false
            if allSame then
              if let some cv := common? then
                consts := consts.insert blk.params[k]! cv

  let mut newBlocks : Array Block := Array.emptyWithCapacity f.blocks.size

  for blk in f.blocks do
    let mut outStmts : Array Stmt := Array.emptyWithCapacity blk.stmts.size
    -- Local CSE table within the current basic block: `(opTag, lhs, rhsOrImm) -> vreg`
    let mut localBinImmCse : Std.HashMap (Nat × VReg × Int) VReg := {}
    for rawStmt in blk.stmts do
      let s0 := substStmt aliases rawStmt
      if s0 != rawStmt then changed := true

      let mut s1 : Stmt := s0
      match s0 with
      | .constImm d v =>
        consts := consts.insert d v
      | .stackAddr d sOff =>
        stackOffs := stackOffs.insert d sOff.toInt
      | .mov d src =>
        if d != src then
          aliases := aliases.insert d src
          if let some c := consts.get? src then consts := consts.insert d c
          if let some ao := addOffs.get? src then addOffs := addOffs.insert d ao
          if let some so := stackOffs.get? src then stackOffs := stackOffs.insert d so
      | .binOp op d l r =>
        match consts.get? l, consts.get? r with
        | some cl, some cr =>
          if let some cv := op.evalConst cl cr then
            changed := true
            consts := consts.insert d cv
            s1 := .constImm d cv
        | _, some cr =>
          match op with
          | .add64 =>
            if cr == 0 then
              changed := true; aliases := aliases.insert d l; s1 := .mov d l
            else if let some so := stackOffs.get? l then
              if let some i32 := fitsInt32U64 cr then
                let total := so + i32.toInt
                if let some s16 := fitsInt16 total then
                  changed := true
                  stackOffs := stackOffs.insert d total
                  s1 := .stackAddr d s16
            else
              match addOffs.get? l, fitsInt32U64 cr with
              | some (base, off1), some i32 =>
                let total := off1 + i32.toInt
                match fitsInt32Int total with
                | some tot32 =>
                  changed := true
                  addOffs := addOffs.insert d (base, total)
                  s1 := .binImm .add64 d base tot32
                | none =>
                  changed := true
                  addOffs := addOffs.insert d (l, i32.toInt)
                  s1 := .binImm .add64 d l i32
              | none, some i32 =>
                changed := true
                addOffs := addOffs.insert d (l, i32.toInt)
                s1 := .binImm .add64 d l i32
              | _, none => pure ()
          | .sub64 =>
            if cr == 0 then
              changed := true; aliases := aliases.insert d l; s1 := .mov d l
            else if let some i32 := fitsInt32U64 cr then
              changed := true
              addOffs := addOffs.insert d (l, -i32.toInt)
              s1 := .binImm .sub64 d l i32
          | .mul64 =>
            if cr == 0 then
              changed := true; consts := consts.insert d 0; s1 := .constImm d 0
            else if cr == 1 then
              changed := true; aliases := aliases.insert d l; s1 := .mov d l
            else
              match log2IfPow2 cr with
              | some k => changed := true; s1 := .binImm .lsh64 d l (Int32.ofInt k)
              | none =>
                if let some i32 := fitsInt32U64 cr then
                  changed := true; s1 := .binImm .mul64 d l i32
          | .div64 =>
            if cr == 1 then
              changed := true; aliases := aliases.insert d l; s1 := .mov d l
            else
              match log2IfPow2 cr with
              | some k => changed := true; s1 := .binImm .rsh64 d l (Int32.ofInt k)
              | none =>
                if let some i32 := fitsInt32U64 cr then
                  changed := true; s1 := .binImm .div64 d l i32
          | .mod64 =>
            if cr == 1 then
              changed := true; consts := consts.insert d 0; s1 := .constImm d 0
            else
              match log2IfPow2 cr with
              | some _ =>
                if let some mask32 := fitsInt32U64 (cr - 1) then
                  changed := true; s1 := .binImm .and64 d l mask32
              | none =>
                if let some i32 := fitsInt32U64 cr then
                  changed := true; s1 := .binImm .mod64 d l i32
          | .or64 =>
            if cr == 0 then changed := true; aliases := aliases.insert d l; s1 := .mov d l
            else if let some i32 := fitsInt32U64 cr then changed := true; s1 := .binImm .or64 d l i32
          | .xor64 =>
            if cr == 0 then changed := true; aliases := aliases.insert d l; s1 := .mov d l
            else if let some i32 := fitsInt32U64 cr then changed := true; s1 := .binImm .xor64 d l i32
          | .and64 =>
            if cr == 0 then changed := true; consts := consts.insert d 0; s1 := .constImm d 0
            else if cr == 0xFFFFFFFFFFFFFFFF then changed := true; aliases := aliases.insert d l; s1 := .mov d l
            else if let some i32 := fitsInt32U64 cr then changed := true; s1 := .binImm .and64 d l i32
          | .lsh64 | .rsh64 | .arsh64 =>
            if (cr &&& 63) == 0 then changed := true; aliases := aliases.insert d l; s1 := .mov d l
            else changed := true; s1 := .binImm op d l (Int32.ofInt (cr &&& 63).toNat)
          | _ =>
            if let some i32 := fitsInt32U64 cr then changed := true; s1 := .binImm op d l i32
        | some _, none =>
          if op.isCommutative then
            changed := true
            s1 := .binOp op d r l
        | none, none =>
          if op == .sub64 && l == r then
            changed := true; consts := consts.insert d 0; s1 := .constImm d 0
          else if op == .xor64 && l == r then
            changed := true; consts := consts.insert d 0; s1 := .constImm d 0
      | .binImm op d l imm =>
        match consts.get? l with
        | some cl =>
          let cr : UInt64 := Int64.toUInt64 (Int64.ofInt imm.toInt)
          if let some cv := op.evalConst cl cr then
            changed := true
            consts := consts.insert d cv
            s1 := .constImm d cv
        | none =>
          if op == .add64 then
            if imm == 0 then
              changed := true; aliases := aliases.insert d l; s1 := .mov d l
            else if let some so := stackOffs.get? l then
              let total := so + imm.toInt
              if let some s16 := fitsInt16 total then
                changed := true
                stackOffs := stackOffs.insert d total
                s1 := .stackAddr d s16
            else
              match addOffs.get? l with
              | some (base, off1) =>
                let total := off1 + imm.toInt
                match fitsInt32Int total with
                | some tot32 =>
                  changed := true
                  addOffs := addOffs.insert d (base, total)
                  s1 := .binImm .add64 d base tot32
                | none =>
                  addOffs := addOffs.insert d (l, imm.toInt)
              | none =>
                addOffs := addOffs.insert d (l, imm.toInt)
          -- Local CSE on `binImm .add64` (eliminates duplicate `acc + 8`, `acc + 88`!)
          if op == .add64 then
            match s1 with
            | .binImm .add64 d2 base2 imm2 =>
              let key : Nat × VReg × Int := (0, base2, imm2.toInt)
              match localBinImmCse.get? key with
              | some prev =>
                changed := true
                aliases := aliases.insert d2 prev
                s1 := .mov d2 prev
              | none =>
                localBinImmCse := localBinImmCse.insert key d2
            | _ => pure ()
      | .cmp op d l r =>
        match consts.get? l, consts.get? r with
        | some cl, some cr =>
          let cv : UInt64 := if op.evalU64 cl cr then 1 else 0
          changed := true
          consts := consts.insert d cv
          s1 := .constImm d cv
        | _, _ =>
          cmpDefs := cmpDefs.insert d (op, l, r)
      | .load sz d base off =>
        if let some so := stackOffs.get? base then
          if let some combined := fitsInt16 (so + off.toInt) then
            changed := true
            s1 := .loadStack sz d combined
        else if let some (base0, k) := addOffs.get? base then
          if let some combined := fitsInt16 (k + off.toInt) then
            changed := true
            s1 := .load sz d base0 combined
      | .store sz base off val =>
        -- Fold stack base, register offset, AND immediate value into 1-insn `storeStackImm` / `storeImm`!
        let valImm? : Option Int32 :=
          match consts.get? val with
          | some cv => fitsInt32U64 cv
          | none => none
        if let some so := stackOffs.get? base then
          if let some combined := fitsInt16 (so + off.toInt) then
            changed := true
            s1 := match valImm? with
              | some i32 => .storeStackImm sz combined i32
              | none => .storeStack sz combined val
        else if let some (base0, k) := addOffs.get? base then
          if let some combined := fitsInt16 (k + off.toInt) then
            changed := true
            s1 := match valImm? with
              | some i32 => .storeImm sz base0 combined i32
              | none => .store sz base0 combined val
        else if let some i32 := valImm? then
          changed := true
          s1 := .storeImm sz base off i32
      | .storeImm sz base off imm =>
        if let some so := stackOffs.get? base then
          if let some combined := fitsInt16 (so + off.toInt) then
            changed := true
            s1 := .storeStackImm sz combined imm
        else if let some (base0, k) := addOffs.get? base then
          if let some combined := fitsInt16 (k + off.toInt) then
            changed := true
            s1 := .storeImm sz base0 combined imm
      | .storeStack sz off val =>
        if let some cv := consts.get? val then
          if let some i32 := fitsInt32U64 cv then
            changed := true
            s1 := .storeStackImm sz off i32
      | _ => pure ()
      outStmts := outStmts.push s1

    -- Optimize terminator: alias substitution + compare-branch fusion + operand flip + const fold
    let t0 := substTerm aliases blk.term
    if t0 != blk.term then changed := true
    let mut t1 : Term := t0
    match t0 with
    | .br c tBlk tArgs eBlk eArgs =>
      match consts.get? c with
      | some cv =>
        changed := true
        t1 := if cv != 0 then .jmp tBlk tArgs else .jmp eBlk eArgs
      | none =>
        match cmpDefs.get? c with
        | some (op, l, r) =>
          let l' := resolveAlias aliases l
          let r' := resolveAlias aliases r
          changed := true
          match consts.get? r' with
          | some cr =>
            match fitsInt32U64 cr with
            | some i32 => t1 := .brCmpImm op l' i32 tBlk tArgs eBlk eArgs
            | none => t1 := .brCmp op l' r' tBlk tArgs eBlk eArgs
          | none =>
            t1 := .brCmp op l' r' tBlk tArgs eBlk eArgs
        | none =>
          changed := true
          t1 := .brCmpImm .ne c 0 tBlk tArgs eBlk eArgs
    | .brCmp op l r tBlk tArgs eBlk eArgs =>
      match consts.get? l, consts.get? r with
      | some cl, some cr =>
        changed := true
        t1 := if op.evalU64 cl cr then .jmp tBlk tArgs else .jmp eBlk eArgs
      | _, some cr =>
        if let some i32 := fitsInt32U64 cr then
          changed := true
          t1 := .brCmpImm op l i32 tBlk tArgs eBlk eArgs
      | some cl, none =>
        if let some i32 := fitsInt32U64 cl then
          changed := true
          t1 := .brCmpImm op.flip r i32 tBlk tArgs eBlk eArgs
      | _, _ => pure ()
    | .brCmpImm op l imm tBlk tArgs eBlk eArgs =>
      match consts.get? l with
      | some cl =>
        let cr : UInt64 := Int64.toUInt64 (Int64.ofInt imm.toInt)
        changed := true
        t1 := if op.evalU64 cl cr then .jmp tBlk tArgs else .jmp eBlk eArgs
      | none =>
        let mut fused := false
        if (op == .eq || op == .ne) && imm == 0 then
          if let some (cOp, a, b) := cmpDefs.get? l then
            let a' := resolveAlias aliases a
            let b' := resolveAlias aliases b
            let effOp := if op == .eq then cOp.invert else cOp
            changed := true
            fused := true
            match consts.get? a', consts.get? b' with
            | some ca, some cb =>
              t1 := if effOp.evalU64 ca cb then .jmp tBlk tArgs else .jmp eBlk eArgs
            | _, some cb =>
              match fitsInt32U64 cb with
              | some i32 => t1 := .brCmpImm effOp a' i32 tBlk tArgs eBlk eArgs
              | none => t1 := .brCmp effOp a' b' tBlk tArgs eBlk eArgs
            | some ca, none =>
              match fitsInt32U64 ca with
              | some i32 => t1 := .brCmpImm effOp.flip b' i32 tBlk tArgs eBlk eArgs
              | none => t1 := .brCmp effOp a' b' tBlk tArgs eBlk eArgs
            | none, none =>
              t1 := .brCmp effOp a' b' tBlk tArgs eBlk eArgs
        if !fused && tBlk == eBlk && tArgs == eArgs then
          changed := true
          t1 := .jmp tBlk tArgs
    | _ => pure ()

    newBlocks := newBlocks.push { blk with stmts := outStmts, term := t1 }

  return ({ f with blocks := newBlocks }, changed)

/-- Dead Code & Dead Block-Parameter Elimination. -/
private def dcePass (f : Func) : Func × Bool := Id.run do
  let mut used : Std.HashSet VReg := {}
  for blk in f.blocks do
    for r in blk.term.usedRegs do
      used := used.insert r
    for s in blk.stmts do
      if s.hasSideEffect then
        for r in s.usedRegs do
          used := used.insert r
  let mut progress := true
  while progress do
    progress := false
    for blk in f.blocks do
      for s in blk.stmts do
        if let some d := s.defReg? then
          if used.contains d then
            for r in s.usedRegs do
              if !used.contains r then
                used := used.insert r
                progress := true

  let mut liveParamMask : Std.HashMap BlockId (Array Bool) := {}
  for blk in f.blocks do
    if !blk.params.isEmpty then
      let mask := blk.params.map (fun p => used.contains p)
      if mask.any (· == false) then
        liveParamMask := liveParamMask.insert blk.id mask

  let filterEdge (tgt : BlockId) (args : Array VReg) : Array VReg :=
    match liveParamMask.get? tgt with
    | none => args
    | some mask => Id.run do
      let mut out : Array VReg := #[]
      for i in [0:min mask.size args.size] do
        if mask[i]! then out := out.push args[i]!
      return out

  let mut changed := false
  let mut newBlocks : Array Block := Array.emptyWithCapacity f.blocks.size
  for blk in f.blocks do
    let newParams :=
      match liveParamMask.get? blk.id with
      | none => blk.params
      | some mask => Id.run do
        let mut ps : Array VReg := #[]
        for i in [0:mask.size] do
          if mask[i]! then ps := ps.push blk.params[i]!
        return ps
    if newParams != blk.params then changed := true
    let newTerm :=
      match blk.term with
      | .jmp t a => .jmp t (filterEdge t a)
      | .br c t ta e ea => .br c t (filterEdge t ta) e (filterEdge e ea)
      | .brCmp op l r t ta e ea => .brCmp op l r t (filterEdge t ta) e (filterEdge e ea)
      | .brCmpImm op l imm t ta e ea => .brCmpImm op l imm t (filterEdge t ta) e (filterEdge e ea)
      | other => other
    if newTerm != blk.term then changed := true
    let mut kept : Array Stmt := Array.emptyWithCapacity blk.stmts.size
    for s in blk.stmts do
      if s.hasSideEffect then
        kept := kept.push s
      else
        match s.defReg? with
        | some d =>
          if used.contains d then kept := kept.push s
          else changed := true
        | none => kept := kept.push s
    newBlocks := newBlocks.push { blk with params := newParams, stmts := kept, term := newTerm }
  return ({ f with blocks := newBlocks }, changed)

/-- Tail Merging + Forwarding-Trampoline Collapse + Unreachable Block Pruning.
    Merges all identical constant-return exit blocks (e.g. multiple `Err.invalidAccountData`
    exits share ONE 2-slot `lddw r0, err; exit` tail block — slashes `.so` size!). -/
private def cfgCleanupPass (f : Func) : Func × Bool := Id.run do
  let mut fwd : Std.HashMap BlockId BlockId := {}
  -- 1. Detect trivial forwarding blocks `bbK(ps): jmp bbT(ps)`
  for blk in f.blocks do
    if blk.id != 0 && blk.stmts.isEmpty then
      match blk.term with
      | .jmp tgt args =>
        if tgt != blk.id && args == blk.params then
          fwd := fwd.insert blk.id tgt
      | _ => pure ()

  -- 2. Tail-merge identical constant-return exit blocks: `bbK(): v = const C; ret v`
  let mut constExitCanon : Std.HashMap UInt64 BlockId := {}
  for blk in f.blocks do
    if blk.id != 0 && blk.params.isEmpty && blk.stmts.size == 1 then
      match blk.stmts[0]!, blk.term with
      | .constImm d cv, .ret rv =>
        if d == rv then
          match constExitCanon.get? cv with
          | some canonId =>
            if canonId != blk.id then
              fwd := fwd.insert blk.id canonId
          | none =>
            constExitCanon := constExitCanon.insert cv blk.id
      | _, _ => pure ()

  let resolveBlk (b : BlockId) : BlockId := Id.run do
    let mut cur := b
    for _ in [0:16] do
      match fwd.get? cur with
      | some nxt => cur := nxt
      | none => break
    return cur

  let mut changed := false
  let mut rewritten : Array Block := Array.emptyWithCapacity f.blocks.size
  for blk in f.blocks do
    let mut t' := blk.term
    match blk.term with
    | .jmp t a =>
      let t2 := resolveBlk t
      if t2 != t then changed := true
      t' := .jmp t2 a
    | .br c t ta e ea =>
      let t2 := resolveBlk t; let e2 := resolveBlk e
      if t2 != t || e2 != e then changed := true
      t' := .br c t2 ta e2 ea
    | .brCmp op l r t ta e ea =>
      let t2 := resolveBlk t; let e2 := resolveBlk e
      if t2 != t || e2 != e then changed := true
      t' := .brCmp op l r t2 ta e2 ea
    | .brCmpImm op l imm t ta e ea =>
      let t2 := resolveBlk t; let e2 := resolveBlk e
      if t2 != t || e2 != e then changed := true
      t' := .brCmpImm op l imm t2 ta e2 ea
    | _ => pure ()
    rewritten := rewritten.push { blk with term := t' }

  -- BFS reachability from block 0
  let mut blkMap : Std.HashMap BlockId Block := {}
  for blk in rewritten do blkMap := blkMap.insert blk.id blk
  let mut visited : Std.HashSet BlockId := {}
  let mut queue : Array BlockId := #[0]
  visited := visited.insert 0
  let mut qi := 0
  while qi < queue.size do
    let bid := queue[qi]!
    qi := qi + 1
    if let some blk := blkMap.get? bid then
      for s in blk.term.succs do
        if !visited.contains s then
          visited := visited.insert s
          queue := queue.push s

  let kept := rewritten.filter (fun b => visited.contains b.id)
  if kept.size != rewritten.size then changed := true
  return ({ f with blocks := kept }, changed)

/-- Run all IR optimization passes to a fixed point (bounded to 12 iterations). -/
def optimizeFunc (f : Func) : Func := Id.run do
  let mut cur := f
  for _ in [0:12] do
    let (f1, c1) := forwardOptPass cur
    let (f2, c2) := dcePass f1
    let (f3, c3) := cfgCleanupPass f2
    cur := f3
    if !c1 && !c2 && !c3 then break
  return cur

end LeanSVM.Compiler
