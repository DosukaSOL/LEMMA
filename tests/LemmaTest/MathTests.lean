/-
  LemmaTest.MathTests — differential tests: compiled `mulDivFloor` / `mulDivCeil` vs exact `Nat`.
-/
import LemmaTest.Harness

namespace LemmaTest.MathTests
open Lean LemmaTest

def W : Nat := 2 ^ 64
def ERR_DIV_ZERO : UInt64 := 0x4C4D0001
def ERR_OVERFLOW : UInt64 := 0x0000001800000000
def ERR_MISMATCH : UInt64 := 0xBAD

/-- Reference: `some q` iff defined and representable. -/
def refMulDiv (ceil : Bool) (a b d : Nat) : Option Nat :=
  if d = 0 then none else
  let q := if ceil then (a * b + d - 1) / d else a * b / d
  if q < W then some q else none

def suite (env : Environment) : TestM Unit := do
  section_ "Lemma.Math.mulDiv: compiled sBPF vs exact Nat (interpreter differential)"
  match compile env `LemmaTest.MathProbes.p_mulDiv with
  | .error e => check false fun _ => s!"p_mulDiv failed to compile: {e}"
  | .ok prog =>
    let edges : List UInt64 := [0, 1, 2, 3, 0xFFFFFFFF, 0x100000000, 0x7FFFFFFFFFFFFFFF,
      0x8000000000000000, 0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF, 1000000007, 10000]
    let mut cases : Array (UInt64 × UInt64 × UInt64) := #[]
    for a in edges do for b in edges do for d in edges do cases := cases.push (a, b, d)
    let mut rng : Rng := ⟨0xC0FFEE⟩
    for _ in [0:1500] do
      let (a, r1) := rng.nextWide; let (b, r2) := r1.nextWide; let (d, r3) := r2.nextWide
      rng := r3; cases := cases.push (a, b, d)
    -- force the 128-bit slow path: large products with a divisor just above the high word
    for _ in [0:1500] do
      let (a, r1) := rng.next; let (b, r2) := r1.next; let (j, r3) := r2.next
      rng := r3
      let hi := (a.toNat * b.toNat) / W
      let d := (hi + 1 + j.toNat % (W - hi - 1)).toUInt64
      cases := cases.push (a, b, d)
    let mut slow := 0
    let mut n := 0
    for (a, b, d) in cases do
      if (a.toNat * b.toNat) ≥ W && d.toNat > (a.toNat * b.toNat) / W then slow := slow + 1
      for ceil in [false, true] do
        let exp := refMulDiv ceil a.toNat b.toNat d.toNat
        let cs : List UInt64 := match exp with
          | some q => [q.toUInt64, q.toUInt64 + 1]
          | none => [0]
        for c in cs do
          let input := u64le a ++ u64le b ++ u64le d ++
            ⟨#[if ceil then 1 else 0, 0, 0, 0, 0, 0, 0, 0]⟩ ++ u64le c
          let (halt, st) := prog.run input
          let want : Sbpf.Halt := match exp with
            | none => .exit (if d == 0 then ERR_DIV_ZERO else ERR_OVERFLOW)
            | some q => if q == c.toNat then .exit 0 else .exit ERR_MISMATCH
          n := n + 1
          check (halt == want) fun _ =>
            s!"mulDiv{if ceil then "Ceil" else "Floor"}({a}, {b}, {d}) c={c}: want {repr want}, got {repr halt} after {st.steps} insns"
    IO.println s!"   mulDivFloor/Ceil: {n} cases, {slow} through the 128-bit division path ({prog.elfSize} B .so)"

end LemmaTest.MathTests
