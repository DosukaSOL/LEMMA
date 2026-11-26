/-
  LemmaTest.VectorTests — replay the committed JSON vectors (`vectors/*.json`) against the
  COMPILED on-chain functions in the interpreter. The same files can be replayed against any
  other implementation (e.g. Rust) to check it against LEMMA's specification.
-/
import Lean.Data.Json
import LemmaTest.Harness
import LemmaTest.Abi

namespace LemmaTest.VectorTests
open Lean LemmaTest

def errCode : String → Option UInt64
  | "divByZero" => some 0x4C4D0001
  | "overflow" => some 0x0000001800000000
  | "invalidArgument" => some 0x0000000200000000
  | _ => none

def getU64 (j : Json) (k : String) : Except String UInt64 := do
  let s ← (← j.getObjVal? k).getStr?
  match s.toNat? with
  | some n => if n < 2^64 then pure n.toUInt64 else throw s!"{k} out of range"
  | none => throw s!"{k} is not a decimal integer"

/-- Expected halt for a case, given a value `c` to compare against. -/
def expectedHalt (j : Json) : Except String (Option UInt64 × Sbpf.Halt) := do
  match j.getObjVal? "expected" with
  | .ok _ => let v ← getU64 j "expected"; pure (some v, .exit 0)
  | .error _ =>
    let e ← (← j.getObjVal? "error").getStr?
    match errCode e with
    | some c => pure (none, .exit c)
    | none => throw s!"unknown error kind {e}"

def replay (env : Environment) (path : String) (probe : Name)
    (encode : Json → Except String ByteArray) (abi : Bool := false) : TestM Unit := do
  let txt ← IO.FS.readFile path
  match Json.parse txt >>= (·.getObjVal? "cases") >>= (·.getArr?) with
  | .error e => check false fun _ => s!"{path}: cannot parse: {e}"
  | .ok cases =>
    match compile env probe with
    | .error e => check false fun _ => s!"{probe}: compile error: {e}"
    | .ok prog =>
      let mut n := 0
      for c in cases do
        match expectedHalt c, encode c with
        | .ok (v?, want), .ok inp =>
          let cval := v?.getD 0
          let wrap (bs : ByteArray) : ByteArray :=
            if abi then (Abi.serialize [] bs (Abi.key32 0xA0)).1 else bs
          let (halt, _) := prog.run (wrap (inp ++ u64le cval))
          n := n + 1
          check (halt == want) fun _ => s!"{path} case {c.compress}: want {repr want}, got {repr halt}"
          -- a wrong value must be detected too (guards against a probe that always succeeds)
          if let some v := v? then
            let (halt2, _) := prog.run (wrap (inp ++ u64le (v + 1)))
            check (halt2 == .exit 0xBAD) fun _ => s!"{path} case {c.compress}: wrong value accepted"
        | .error e, _ | _, .error e => check false fun _ => s!"{path}: bad case {c.compress}: {e}"
      IO.println s!"   {path}: {n} vectors replayed against compiled {probe}{if abi then " (ABI-serialized input)" else ""}"

def suite (env : Environment) : TestM Unit := do
  section_ "JSON test vectors replayed against compiled programs (interpreter)"
  for (path, ceil) in [("vectors/mulDivFloor.json", false), ("vectors/mulDivCeil.json", true)] do
    replay env path `LemmaTest.MathProbes.p_mulDiv fun j => do
      pure (u64le (← getU64 j "a") ++ u64le (← getU64 j "b") ++ u64le (← getU64 j "d") ++
        ⟨#[if ceil then 1 else 0, 0, 0, 0, 0, 0, 0, 0]⟩)
  replay env "vectors/swapOut.json" `LemmaTest.MathProbes.p_swap fun j => do
    pure (u64le (← getU64 j "reserveIn") ++ u64le (← getU64 j "reserveOut") ++
      u64le (← getU64 j "amountIn") ++ u64le (← getU64 j "feeBps"))
  -- the real-SVM probes (same programs the LiteSVM job runs), with ABI-serialized input
  for (path, ceil) in [("vectors/mulDivFloor.json", false), ("vectors/mulDivCeil.json", true)] do
    replay env path `LemmaTest.ChainProbes.mulDiv (abi := true) fun j => do
      pure (u64le (← getU64 j "a") ++ u64le (← getU64 j "b") ++ u64le (← getU64 j "d") ++
        ⟨#[if ceil then 1 else 0]⟩)
  replay env "vectors/swapOut.json" `LemmaTest.ChainProbes.swap (abi := true) fun j => do
    pure (u64le (← getU64 j "reserveIn") ++ u64le (← getU64 j "reserveOut") ++
      u64le (← getU64 j "amountIn") ++ u64le (← getU64 j "feeBps"))

end LemmaTest.VectorTests
