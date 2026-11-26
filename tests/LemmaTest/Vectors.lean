/-
  LemmaTest.Vectors — reference test vectors for `Lemma.Math`, computed from the plain `Nat`
  specification (NOT from the implementation), so they can check any implementation in any
  language. All integers are decimal strings (u64 values exceed JavaScript's safe range).
-/
import LemmaTest.Harness

namespace LemmaTest.Vectors
open LemmaTest

def W : Nat := 2 ^ 64

inductive Outcome where
  | ok (v : Nat)
  | err (code : String)
  deriving Repr, BEq

def Outcome.json : Outcome → String
  | .ok v => s!"\"expected\": \"{v}\""
  | .err c => s!"\"error\": \"{c}\""

/-- Reference `mulDiv` (floor or ceil), with the same error classification as the on-chain code. -/
def refMulDiv (ceil : Bool) (a b d : Nat) : Outcome :=
  if d = 0 then .err "divByZero" else
  let q := if ceil then (a * b + d - 1) / d else a * b / d
  if q < W then .ok q else .err "overflow"

/-- Reference constant-product swap quote (same error order as `swapOutM`). -/
def refSwap (x y amt fee : Nat) : Outcome :=
  if fee > 10000 then .err "invalidArgument" else
  let aif := amt * (10000 - fee) / 10000
  if x + aif ≥ W then .err "overflow" else
  if x + aif = 0 then .err "divByZero" else
  .ok (y * aif / (x + aif))

def edges : List UInt64 :=
  [0, 1, 2, 3, 9999, 10000, 10001, 0xFFFFFFFF, 0x100000000, 1000000007,
   0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF]

structure MulDivCase where
  a : UInt64
  b : UInt64
  d : UInt64

def mulDivCases : Array MulDivCase := Id.run do
  let mut cs := #[]
  for a in edges do for b in edges do for d in edges do cs := cs.push ⟨a, b, d⟩
  let mut rng : Rng := ⟨0x5EC7095⟩
  for _ in [0:600] do
    let (a, r1) := rng.nextWide; let (b, r2) := r1.nextWide; let (d, r3) := r2.nextWide
    rng := r3; cs := cs.push ⟨a, b, d⟩
  return cs

structure SwapCase where
  x : UInt64
  y : UInt64
  amt : UInt64
  fee : UInt64

def swapCases : Array SwapCase := Id.run do
  let fees : List UInt64 := [0, 1, 5, 30, 100, 9999, 10000, 10001]
  let sizes : List UInt64 := [0, 1, 1000, 1000000, 0xFFFFFFFF, 0x7FFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF]
  let mut cs := #[]
  for x in sizes do for y in sizes do for amt in sizes do for fee in fees do
    cs := cs.push ⟨x, y, amt, fee⟩
  let mut rng : Rng := ⟨0x5A9⟩
  for _ in [0:600] do
    let (x, r1) := rng.nextWide; let (y, r2) := r1.nextWide; let (amt, r3) := r2.nextWide
    let (f, r4) := r3.next
    rng := r4; cs := cs.push ⟨x, y, amt, f % 10002⟩
  return cs

def mulDivJson (ceil : Bool) : String := Id.run do
  let name := if ceil then "mulDivCeil" else "mulDivFloor"
  let formula := if ceil then "ceil(a*b/d)" else "floor(a*b/d)"
  let mut lines : Array String := #[]
  for c in mulDivCases do
    let o := refMulDiv ceil c.a.toNat c.b.toNat c.d.toNat
    lines := lines.push s!"    \{\"a\": \"{c.a}\", \"b\": \"{c.b}\", \"d\": \"{c.d}\", {o.json}}"
  return s!"\{\n  \"function\": \"{name}\",\n  \"spec\": \"{formula} over unbounded integers; error divByZero if d = 0; error overflow if the result is >= 2^64\",\n  \"generator\": \"lake exe lemma-vectors --write (computed from the Nat specification, not the implementation)\",\n  \"cases\": [\n" ++
    ",\n".intercalate lines.toList ++ "\n  ]\n}\n"

def swapJson : String := Id.run do
  let mut lines : Array String := #[]
  for c in swapCases do
    let o := refSwap c.x.toNat c.y.toNat c.amt.toNat c.fee.toNat
    lines := lines.push s!"    \{\"reserveIn\": \"{c.x}\", \"reserveOut\": \"{c.y}\", \"amountIn\": \"{c.amt}\", \"feeBps\": \"{c.fee}\", {o.json}}"
  return "{\n  \"function\": \"swapOut\",\n  \"spec\": \"aif = floor(amountIn*(10000-feeBps)/10000); out = floor(reserveOut*aif/(reserveIn+aif)); errors in order: invalidArgument if feeBps > 10000, overflow if reserveIn+aif >= 2^64, divByZero if reserveIn+aif = 0\",\n  \"generator\": \"lake exe lemma-vectors --write (computed from the Nat specification, not the implementation)\",\n  \"cases\": [\n" ++
    ",\n".intercalate lines.toList ++ "\n  ]\n}\n"

def files : List (String × String) :=
  [("vectors/mulDivFloor.json", mulDivJson false),
   ("vectors/mulDivCeil.json", mulDivJson true),
   ("vectors/swapOut.json", swapJson)]

end LemmaTest.Vectors
