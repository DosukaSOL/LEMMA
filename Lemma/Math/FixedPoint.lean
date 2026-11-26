/-
  Lemma.Math.FixedPoint — fixed-point multiply/divide with an explicit rounding direction.

  A fixed-point number `x` with scale `S` represents `x / S`. All operations take the scale as an
  argument (e.g. `S = 10^9` or `2^32`) and inherit their guarantees from `mulDiv`:

  * `fpMul r x y S = q` (floor) satisfies `q·S ≤ x·y < (q+1)·S`
  * `fpMul r x y S = q` (ceil)  satisfies `x·y ≤ q·S < x·y + S`
  * `fpDiv r x y S` = `mulDiv r x S y`: (floor) `q·y ≤ x·S < (q+1)·y`; (ceil) `x·S ≤ q·y < x·S + y`
-/
import Lemma.Math.MulDiv

namespace Lemma.Math
open LeanSVM Spec

/-- Fixed-point product `x·y / S` with the requested rounding. -/
@[inline] def fpMulM (r : Rounding) (x y scale : UInt64) : SolanaM UInt64 := mulDivM r x y scale

/-- Fixed-point quotient `x·S / y` with the requested rounding. -/
@[inline] def fpDivM (r : Rounding) (x y scale : UInt64) : SolanaM UInt64 := mulDivM r x scale y

/-- Two-sided bounds of a successful floor `mulDiv`: `q·d ≤ a·b < (q+1)·d`. -/
theorem mulDivFloorM_bounds (a b d q : UInt64) (s s' : SvmState)
    (h : mulDivFloorM a b d s = .ok q s') :
    q.toNat * d.toNat ≤ a.toNat * b.toNat ∧ a.toNat * b.toNat < (q.toNat + 1) * d.toNat := by
  obtain ⟨-, hd, -, hq⟩ := (mulDivFloorM_ok_iff a b d q s s').mp h
  rw [hq]
  refine ⟨Nat.div_mul_le_self _ _, ?_⟩
  rw [Nat.add_mul, Nat.one_mul]
  generalize a.toNat * b.toNat = X
  have e := Nat.div_add_mod X d.toNat
  have m := Nat.mod_lt X (show 0 < d.toNat by omega)
  have c : X / d.toNat * d.toNat = d.toNat * (X / d.toNat) := Nat.mul_comm _ _
  omega

/-- Two-sided bounds of a successful ceil `mulDiv`: `a·b ≤ q·d < a·b + d`. -/
theorem mulDivCeilM_bounds (a b d q : UInt64) (s s' : SvmState)
    (h : mulDivCeilM a b d s = .ok q s') :
    a.toNat * b.toNat ≤ q.toNat * d.toNat ∧ q.toNat * d.toNat < a.toNat * b.toNat + d.toNat := by
  obtain ⟨-, hd, -, hq⟩ := (mulDivCeilM_ok_iff a b d q s s').mp h
  rw [hq]; unfold ceilDiv
  generalize a.toNat * b.toNat = X
  generalize hD : d.toNat = D at hd
  have hD0 : 0 < D := by omega
  have h1 := Nat.div_add_mod (X + D - 1) D
  have h2 := Nat.mod_lt (X + D - 1) hD0
  rw [Nat.mul_comm] at h1
  constructor <;> omega

theorem fpMulM_floor_bounds (x y S q : UInt64) (s s' : SvmState)
    (h : fpMulM .floor x y S s = .ok q s') :
    q.toNat * S.toNat ≤ x.toNat * y.toNat ∧ x.toNat * y.toNat < (q.toNat + 1) * S.toNat :=
  mulDivFloorM_bounds x y S q s s' h

theorem fpMulM_ceil_bounds (x y S q : UInt64) (s s' : SvmState)
    (h : fpMulM .ceil x y S s = .ok q s') :
    x.toNat * y.toNat ≤ q.toNat * S.toNat ∧ q.toNat * S.toNat < x.toNat * y.toNat + S.toNat :=
  mulDivCeilM_bounds x y S q s s' h

theorem fpDivM_floor_bounds (x y S q : UInt64) (s s' : SvmState)
    (h : fpDivM .floor x y S s = .ok q s') :
    q.toNat * y.toNat ≤ x.toNat * S.toNat ∧ x.toNat * S.toNat < (q.toNat + 1) * y.toNat :=
  mulDivFloorM_bounds x S y q s s' h

theorem fpDivM_ceil_bounds (x y S q : UInt64) (s s' : SvmState)
    (h : fpDivM .ceil x y S s = .ok q s') :
    x.toNat * S.toNat ≤ q.toNat * y.toNat ∧ q.toNat * y.toNat < x.toNat * S.toNat + y.toNat :=
  mulDivCeilM_bounds x S y q s s' h

end Lemma.Math
