/-
  Lemma.Math.Witnesses — non-vacuity witnesses, checked by the kernel.

  Many theorems in `Lemma.Math` have the form "if the on-chain function succeeds, then P". Such a
  theorem would be vacuous if the function could never succeed. Each witness below exhibits a
  concrete successful run (evaluated by `decide`, i.e. by the kernel, with no native code).
  The differential tests additionally exercise thousands of successful runs.
-/
import Lemma.Math.ConstantProduct
import Lemma.Math.FixedPoint

namespace Lemma.Math.Witnesses
open LeanSVM Lemma.Math

/-- Extract the result of a run (proof device for the witnesses). -/
def result? {α} (r : SvmStep α) : Option α :=
  match r with
  | .ok v _ => some v
  | .err _ _ => none

theorem mulDivFloorM_can_succeed : result? (mulDivFloorM 7 6 4 SvmState.empty) = some 10 := by decide
theorem mulDivCeilM_can_succeed : result? (mulDivCeilM 7 6 4 SvmState.empty) = some 11 := by decide

/-- A 0.30% fee swap of 1,000 into a 1,000,000 / 1,000,000 pool quotes 996. -/
theorem swapOutM_can_succeed :
    result? (swapOutM 1000000 1000000 1000 30 SvmState.empty) = some 996 := by decide

theorem fpMulM_can_succeed :
    result? (fpMulM .floor 1500000000 2500000000 1000000000 SvmState.empty) = some 3750000000 := by
  decide

end Lemma.Math.Witnesses
