/-
  LeanSVM.SBPF.Peephole
  Machine-level sBPF peephole optimizer: shrinks 64-bit immediates to 1-slot mov64/mov32,
  eliminates redundant moves, no-op ALU ops, fallthrough jumps, unreachable code, and
  folds immediate comparisons directly into conditional jump instructions.
-/
import LeanSVM.SBPF.ISA

namespace LeanSVM.SBPF

/-- Check if a `UInt64` fits in a signed 32-bit immediate (`[-2^31, 2^31 - 1]`). -/
def fitsInt32 (v : UInt64) : Option Int32 :=
  if v <= 0x7FFFFFFF then
    some (Int32.ofInt (v.toNat : Int))
  else if v >= 0xFFFFFFFF80000000 then
    let neg := (0x10000000000000000 - v.toNat : Nat)
    some (Int32.ofInt (-(neg : Int)))
  else
    none

/-- Check if a `UInt64` fits in an unsigned 32-bit immediate (`[0, 2^32 - 1]`).
    In sBPF, `mov32 dst, imm` zero-extends `imm` to 64 bits in 1 slot (saving 8 bytes over `lddw`). -/
def fitsUInt32 (v : UInt64) : Option Int32 :=
  if v <= 0xFFFFFFFF then
    some (UInt32.toInt32 v.toUInt32)
  else
    none

/-- Shrink a single instruction (e.g. `lddw` -> `mov64`/`mov32`, `mul 2^k` -> `lsh k`). -/
def shrinkInsn : Insn → Option Insn
  | .alu64Reg .mov d s => if d == s then none else some (.alu64Reg .mov d s)
  | .alu32Reg .mov d s => if d == s then none else some (.alu32Reg .mov d s)
  | .alu64Imm .add _ 0 => none
  | .alu64Imm .sub _ 0 => none
  | .alu64Imm .or  _ 0 => none
  | .alu64Imm .xor _ 0 => none
  | .alu64Imm .lsh _ 0 => none
  | .alu64Imm .rsh _ 0 => none
  | .alu64Imm .arsh _ 0 => none
  | .alu64Imm .mul _ 1 => none
  | .alu64Imm .div _ 1 => none
  | .alu64Imm .mul d 0 => some (.alu64Imm .mov d 0)
  | .alu64Imm .and d 0 => some (.alu64Imm .mov d 0)
  | .lddw d imm =>
    match fitsInt32 imm with
    | some i32 => some (.alu64Imm .mov d i32)
    | none =>
      match fitsUInt32 imm with
      | some i32 => some (.alu32Imm .mov d i32)
      | none => some (.lddw d imm)
  | insn => some insn

/-- Single pass of peephole optimizations on a symbolic sBPF instruction stream. -/
private def peepholePass (insns : Array Insn) : Array Insn × Bool := Id.run do
  -- Pre-scan labels that immediately point to `.exit` (for jump-to-exit forwarding!)
  let mut exitLabels : List String := []
  let n := insns.size
  for k in [0:n] do
    match insns[k]! with
    | .label lbl =>
      if k + 1 < n then
        match insns[k + 1]! with
        | .exit => if !exitLabels.contains lbl then exitLabels := lbl :: exitLabels
        | _ => pure ()
    | _ => pure ()

  let mut out : Array Insn := Array.emptyWithCapacity n
  let mut changed := false
  let mut i := 0
  let mut dead := false
  while i < n do
    let cur := insns[i]!
    -- Drop unreachable instructions after `exit` or `ja` until next label
    if dead then
      match cur with
      | .label _ =>
        dead := false
        out := out.push cur
        i := i + 1
        continue
      | _ =>
        changed := true
        i := i + 1
        continue

    -- Single-instruction shrinking
    match shrinkInsn cur with
    | none =>
      changed := true
      i := i + 1
      continue
    | some shrunk =>
      if shrunk != cur then changed := true
      -- Three-instruction window peepholes (e.g. `mov/lddw rX, c; mov r0, rX; exit` -> `mov/lddw r0, c; exit`)
      if i + 2 < n then
        let nxt := insns[i + 1]!
        let nxt2 := insns[i + 2]!
        match shrunk, nxt, nxt2 with
        | .alu64Imm .mov x imm, .alu64Reg .mov d x2, .exit =>
          if d == Reg.r0 && x == x2 then
            out := out.push (.alu64Imm .mov Reg.r0 imm) |>.push .exit
            dead := true
            changed := true
            i := i + 3
            continue
        | .alu32Imm .mov x imm, .alu64Reg .mov d x2, .exit =>
          if d == Reg.r0 && x == x2 then
            out := out.push (.alu32Imm .mov Reg.r0 imm) |>.push .exit
            dead := true
            changed := true
            i := i + 3
            continue
        | .lddw x imm, .alu64Reg .mov d x2, .exit =>
          if d == Reg.r0 && x == x2 then
            out := out.push (.lddw Reg.r0 imm) |>.push .exit
            dead := true
            changed := true
            i := i + 3
            continue
        | .alu64Reg .mov x y, .alu64Reg .mov d x2, .exit =>
          if d == Reg.r0 && x == x2 then
            out := out.push (.alu64Reg .mov Reg.r0 y) |>.push .exit
            dead := true
            changed := true
            i := i + 3
            continue
        -- Branch-over-jump inversion: `jcc cond, L1; ja L2; L1:` -> `jcc (invert cond), L2; L1:`!
        | .jccReg cond d s l1, .ja l2, .label l1' =>
          if l1 == l1' then
            if let some inv := cond.invert then
              out := out.push (.jccReg inv d s l2) |>.push (.label l1')
              changed := true
              i := i + 3
              continue
        | .jccImm cond d imm l1, .ja l2, .label l1' =>
          if l1 == l1' then
            if let some inv := cond.invert then
              out := out.push (.jccImm inv d imm l2) |>.push (.label l1')
              changed := true
              i := i + 3
              continue
        | _, _, _ => pure ()

      -- Jump-to-exit forwarding: `ja exit_lbl` -> `exit`! (Turns `call fn; ja exit` into `call fn; exit`!)
      match shrunk with
      | .ja tgt =>
        if exitLabels.contains tgt then
          out := out.push .exit
          dead := true
          changed := true
          i := i + 1
          continue
      | _ => pure ()

      -- Two-instruction window peepholes
      if i + 1 < n then
        let nxt := insns[i + 1]!
        match shrunk, nxt with
        -- `ja L` immediately followed by `L:` -> eliminate jump!
        | .ja tgt, .label lbl =>
          if tgt == lbl then
            changed := true
            i := i + 1
            continue
        -- `mov64 rA, rB; ldx rA, [rA+off]` -> `ldx rA, [rB+off]`!
        | .alu64Reg .mov a b, .ldx sz d s off =>
          if a == d && a == s then
            out := out.push (.ldx sz d b off)
            changed := true
            i := i + 2
            continue
        -- `mov64 rA, rB; mov64 rB, rA` -> drop second move
        | .alu64Reg .mov a b, .alu64Reg .mov b2 a2 =>
          if a == a2 && b == b2 then
            out := out.push shrunk
            changed := true
            i := i + 2
            continue
        -- `mov64 rA, imm; mov64 rA, imm2` -> drop dead first mov
        | .alu64Imm .mov a _, .alu64Imm .mov a2 _ =>
          if a == a2 then
            changed := true
            i := i + 1
            continue
        -- `mov64 rA, rB; mov64 rA, imm` -> drop dead first mov
        | .alu64Reg .mov a _, .alu64Imm .mov a2 _ =>
          if a == a2 then
            changed := true
            i := i + 1
            continue
        -- `mov64 rA, imm; mov64 rA, rB` (when a != b) -> drop dead first mov
        | .alu64Imm .mov a _, .alu64Reg .mov a2 b2 =>
          if a == a2 && a != b2 then
            changed := true
            i := i + 1
            continue
        -- Store-to-reload forwarding: `stx [base+off], rA; ldx rA, [base+off]` -> drop reload!
        | .stx sz1 b1 s1 off1, .ldx sz2 d2 b2 off2 =>
          if sz1 == sz2 && b1 == b2 && off1 == off2 then
            if d2 == s1 then
              out := out.push shrunk
              changed := true
              i := i + 2
              continue
            else
              out := out.push shrunk |>.push (.alu64Reg .mov d2 s1)
              changed := true
              i := i + 2
              continue
        -- `add64 r, k1; add64 r, k2` -> combine immediates!
        | .alu64Imm .add r1 k1, .alu64Imm .add r2 k2 =>
          if r1 == r2 then
            let sum : Int := k1.toInt + k2.toInt
            if sum >= -2147483648 && sum <= 2147483647 then
              if sum != 0 then
                out := out.push (.alu64Imm .add r1 (Int32.ofInt sum))
              changed := true
              i := i + 2
              continue
        | _, _ => pure ()

      -- Check if `shrunk` starts a dead region
      match shrunk with
      | .exit | .ja _ => dead := true
      | _ => pure ()
      out := out.push shrunk
      i := i + 1

  -- Remove unreferenced labels (except `entrypoint` and function labels kept for clarity)
  let mut usedLabels : List String := []
  for insn in out do
    match insn with
    | .ja t | .jccReg _ _ _ t | .jccImm _ _ _ t | .callLocal t =>
      if !usedLabels.contains t then usedLabels := t :: usedLabels
    | _ => pure ()
  let mut finalOut : Array Insn := Array.emptyWithCapacity out.size
  for insn in out do
    match insn with
    | .label name =>
      if name == "entrypoint" || usedLabels.contains name then
        finalOut := finalOut.push insn
      else
        changed := true
    | _ => finalOut := finalOut.push insn
  return (finalOut, changed)

/-- Basic-block register value tracking pass:
    Eliminates redundant constant rematerializations (`mov64/mov32/lddw` of a value
    already in `dst`) and redundant stack-spill reloads (`ldxdw dst, [r10+off]` when
    `dst` already holds `[r10+off]`) within each straight-line basic block! -/
private def bbValueTrackPass (insns : Array Insn) : Array Insn × Bool := Id.run do
  let mut out : Array Insn := Array.emptyWithCapacity insns.size
  let mut changed := false
  let mut regConst : Array (Option UInt64) := Array.replicate 11 none
  let mut regStack : Array (Option Int16)  := Array.replicate 11 none

  let resetAll := (Array.replicate 11 (none : Option UInt64), Array.replicate 11 (none : Option Int16))
  let clearSlot (rs : Array (Option Int16)) (off : Int16) : Array (Option Int16) :=
    rs.map (fun o => if o == some off then none else o)
  let immVal32 (i : Int32) : UInt64 := Int64.toUInt64 (Int64.ofInt i.toInt)
  let uimmVal32 (i : Int32) : UInt64 := (Int32.toUInt32 i).toUInt64

  for insn in insns do
    match insn with
    | .label _ =>
      let (rc, rs) := resetAll
      regConst := rc; regStack := rs
      out := out.push insn
    | .callLocal _ | .callSyscall _ =>
      -- Caller-saved r0..r5 clobbered; conservatively clear all stack slot tracking
      -- (callee may write via stack out-pointer), preserve `regConst` on callee-saved r6..r9!
      for idx in [0:6] do
        regConst := regConst.set! idx none
      regStack := Array.replicate 11 none
      out := out.push insn
    | .exit | .ja _ =>
      let (rc, rs) := resetAll
      regConst := rc; regStack := rs
      out := out.push insn
    | .alu64Imm .mov d imm =>
      let v := immVal32 imm
      let di := d.idx.toNat
      if regConst[di]! == some v then
        changed := true
      else
        regConst := regConst.set! di (some v)
        regStack := regStack.set! di none
        out := out.push insn
    | .alu32Imm .mov d imm =>
      let v := uimmVal32 imm
      let di := d.idx.toNat
      if regConst[di]! == some v then
        changed := true
      else
        regConst := regConst.set! di (some v)
        regStack := regStack.set! di none
        out := out.push insn
    | .lddw d v =>
      let di := d.idx.toNat
      if regConst[di]! == some v then
        changed := true
      else
        regConst := regConst.set! di (some v)
        regStack := regStack.set! di none
        out := out.push insn
    | .alu64Reg .mov d s =>
      let di := d.idx.toNat
      let si := s.idx.toNat
      if d == s || (regConst[di]!.isSome && regConst[di]! == regConst[si]!) ||
         (regStack[di]!.isSome && regStack[di]! == regStack[si]!) then
        changed := true
      else
        regConst := regConst.set! di regConst[si]!
        regStack := regStack.set! di regStack[si]!
        out := out.push insn
    | .ldx .b8 d base off =>
      let di := d.idx.toNat
      if base == Reg.r10 && regStack[di]! == some off then
        changed := true
      else
        regConst := regConst.set! di none
        regStack := regStack.set! di (if base == Reg.r10 then some off else none)
        out := out.push insn
    | .stx .b8 base s off =>
      let si := s.idx.toNat
      if base == Reg.r10 && regStack[si]! == some off then
        changed := true
      else
        if base == Reg.r10 then
          regStack := clearSlot regStack off
          regStack := regStack.set! si (some off)
        else
          -- Indirect store could alias a stack buffer pointer (e.g. outBuf)
          regStack := Array.replicate 11 none
        out := out.push insn
    | .stx _ base _ _ | .stImm _ base _ _ =>
      let _ := base
      regStack := Array.replicate 11 none
      out := out.push insn
    | .ldx _ d _ _ | .alu64Reg _ d _ | .alu64Imm _ d _ | .alu32Reg _ d _
    | .alu32Imm _ d _ | .neg64 d | .lddwRodata d _ =>
      let di := d.idx.toNat
      regConst := regConst.set! di none
      regStack := regStack.set! di none
      out := out.push insn
    | .jccReg _ _ _ _ | .jccImm _ _ _ _ =>
      out := out.push insn
  return (out, changed)

/-- Run peephole optimization to a fixed point (bounded to 8 iterations). -/
def peepholeOptimize (insns : Array Insn) : Array Insn := Id.run do
  let mut cur := insns
  for _ in [0:8] do
    let (next1, c1) := peepholePass cur
    let (next2, c2) := bbValueTrackPass next1
    cur := next2
    if !c1 && !c2 then break
  return cur

end LeanSVM.SBPF
