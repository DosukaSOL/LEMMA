/-
  `lake exe lemma-test` — runs every LEMMA test suite that does not need network access.
  Exit code 0 iff all checks pass.
-/
import LemmaTest.Harness
import LemmaTest.NatTests

open Lean LemmaTest

def main : IO UInt32 := do
  let env ← loadEnv #[`LemmaTest.NatProbes]
  let ((), report) ← (do
      NatTests.suite env
    : TestM Unit).run {}
  IO.println s!"\n{report.passed} checks passed, {report.failed.size} failed"
  for f in report.failed[:min 40 report.failed.size] do IO.println s!"  FAIL {f}"
  return if report.failed.isEmpty then 0 else 1
