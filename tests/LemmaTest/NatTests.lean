/-
  LemmaTest.NatTests — differential tests for LEMMA patch 0001 (sound `Nat` lowering).

  For each probe and input `(a, b)`, the reference model evaluates the same `Nat` expression with
  overflow tracking. Required compiled behaviour ("exact or abort"):
  * if every intermediate value is `< 2^64`: identical result to Lean
    (success iff the expression equals `c`);
  * otherwise: the program aborts (Solana `abort` syscall).
-/
import LemmaTest.Harness
import LeanSVM

namespace LemmaTest.NatTests
open Lean LemmaTest

def W : Nat := 2 ^ 64

/-- Overflow-tracked `Nat`: `none` once any intermediate is `≥ 2^64`. -/
abbrev CNat := Option Nat
def lift (n : Nat) : CNat := if n < W then some n else none
def cadd (x y : CNat) : CNat := do lift ((← x) + (← y))
def cmul (x y : CNat) : CNat := do lift ((← x) * (← y))
def csub (x y : CNat) : CNat := do pure ((← x) - (← y))
def cdiv (x y : CNat) : CNat := do pure ((← x) / (← y))
def cmod (x y : CNat) : CNat := do pure ((← x) % (← y))

def sumToC : Nat → CNat → CNat
  | 0, acc => acc
  | n + 1, acc => sumToC n (cadd (cadd acc (some n)) (some 1))

/-- Reference model: `some (some v)` = value `v`; `some none` = must abort;
    `none` = precondition rejected (expect the probe's error code). -/
def model (probe : String) (a b : Nat) : Option CNat :=
  match probe with
  | "p_add"   => some (cadd a b)
  | "p_sub"   => some (csub a b)
  | "p_mul"   => some (cmul a b)
  | "p_div"   => some (cdiv a b)
  | "p_mod"   => some (cmod a b)
  | "p_chain" => some (cdiv (cmul a b) (cadd b (some 1)))
  | "p_trunc32" => some ((cadd a b).map fun s => min s (2 ^ 32 - 1))
  | "p_pred"  => some (some (a - 1))
  | "p_loop"  => if b ≤ 64 then some (sumToC b a) else none
  | _ => none

def errInvalidArgument : UInt64 := 0x0000000200000000

def edges : List UInt64 :=
  [0, 1, 2, 3, 7, 0x7FFFFFFF, 0xFFFFFFFE, 0xFFFFFFFF, 0x100000000, 0x100000001,
   0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF]

def runProbe (env : Environment) (probe : String) (randomCases : Nat) : TestM Unit := do
  let name := Name.mkStr `LemmaTest.NatProbes probe
  match compile env name with
  | .error e => check false fun _ => s!"{probe}: failed to compile: {e}"
  | .ok prog =>
    let mut inputs : Array (UInt64 × UInt64) := #[]
    for a in edges do
      for b in edges do inputs := inputs.push (a, b)
    let mut rng : Rng := ⟨0x5EED0001 + probe.length.toUInt64⟩
    for _ in [0:randomCases] do
      let (a, r1) := rng.nextWide
      let (b, r2) := r1.nextWide
      rng := r2
      inputs := inputs.push (a, b)
    -- keep loop probe cheap: also test small b explicitly
    if probe == "p_loop" then
      for b in [0:66] do inputs := inputs.push (0xFFFFFFFFFFFFF000, b.toUInt64)
    let mut n := 0
    for (a, b) in inputs do
      let exp := model probe a.toNat b.toNat
      let cs : List UInt64 := match exp with
        | some (some v) => if v < W then [v.toUInt64, v.toUInt64 + 1] else [0]
        | _ => [0, 12345]
      for c in cs do
        let input := u64le a ++ u64le b ++ u64le c
        let (halt, _) := prog.run input
        let want : Sbpf.Halt := match exp with
          | none => .exit errInvalidArgument
          | some none => .abort
          | some (some v) => if v == c.toNat then .exit 0 else .exit errInvalidArgument
        n := n + 1
        check (halt == want) fun _ =>
          s!"{probe}(a={a}, b={b}, c={c}): expected {repr want}, interpreter gave {repr halt}"
    IO.println s!"   {probe}: {n} cases ({prog.elfSize} B .so)"

def suite (env : Environment) : TestM Unit := do
  section_ "LEMMA patch 0001: Nat lowering is exact-or-abort (interpreter differential)"
  for p in ["p_add", "p_sub", "p_mul", "p_div", "p_mod", "p_chain", "p_trunc32", "p_pred",
            "p_loop"] do
    runProbe env p 300
  -- compile-time rejection of literals that do not fit in 64 bits
  match compile env `LemmaTest.NatProbes.p_bigLiteral with
  | .ok _ => check false fun _ => "p_bigLiteral: compiled, but a 2^64 literal must be rejected"
  | .error e =>
    check ((e.splitOn "does not fit in 64 bits").length > 1) fun _ =>
      s!"p_bigLiteral: rejected for the wrong reason: {e}"
    IO.println "   p_bigLiteral: rejected at compile time ✓"

end LemmaTest.NatTests
