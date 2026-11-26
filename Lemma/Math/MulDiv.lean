/-
  Lemma.Math.MulDiv — `a * b / d` with an explicit rounding direction and a 128-bit
  intermediate, so it is correct for every input whose rounded result fits in 64 bits.

  Specification (both proved, kernel-checked):
  * `mulDivFloor a b d = some q  ↔  d ≠ 0 ∧ ⌊a·b/d⌋ < 2^64 ∧ q = ⌊a·b/d⌋`
  * `mulDivCeil  a b d = some q  ↔  d ≠ 0 ∧ ⌈a·b/d⌉ < 2^64 ∧ q = ⌈a·b/d⌉`

  So `none` is returned exactly when the true result is undefined (`d = 0`) or does not fit.
  The function never overflows silently. "No overflow for all valid inputs" holds because
  `some` is returned for every input whose rounded result is representable.
-/
import Lemma.Math.Wide
import Lemma.Errors

namespace Lemma.Math
open LeanSVM

/-- Rounding direction. Callers choose the direction that favours the protocol. -/
inductive Rounding where
  | floor
  | ceil
  deriving Repr, DecidableEq

/-- `⌊a·b/d⌋`, or `none` if `d = 0` or the result does not fit in 64 bits. -/
def mulDivFloor (a b d : UInt64) : Option UInt64 :=
  if d == 0 then none else
  let w := mulWide a b
  if w.1 == 0 then some (w.2 / d)            -- fast path: product fits in 64 bits
  else if w.1 ≥ d then none                  -- quotient would need more than 64 bits
  else some (div128 w.1 w.2 d)

/-- `⌈a·b/d⌉`, or `none` if `d = 0` or the result does not fit in 64 bits. -/
def mulDivCeil (a b d : UInt64) : Option UInt64 :=
  if d == 0 then none else
  let w := mulWide a b
  if w.1 != 0 && w.1 ≥ d then none else
  let q := if w.1 == 0 then w.2 / d else div128 w.1 w.2 d
  let r := w.2 - q * d                           -- exact remainder (it is < d < 2^64)
  if r == 0 then some q
  else if q == 0xFFFFFFFFFFFFFFFF then none      -- ⌈·⌉ = 2^64 does not fit
  else some (q + 1)

@[inline] def mulDiv (r : Rounding) (a b d : UInt64) : Option UInt64 :=
  match r with
  | .floor => mulDivFloor a b d
  | .ceil => mulDivCeil a b d

/-! ### On-chain versions

lean-svm cannot pass an `Option` payload through a join point (see patch 0002), so programs use
these `SolanaM` versions. They fail with `LErr.divByZero` when `d = 0` and with
`Err.arithmeticOverflow` when the result does not fit. `mulDivFloorM_eq` / `mulDivCeilM_eq` prove
they agree exactly with the pure functions above, so the `_spec` theorems carry over. -/

/-- Error code for a `none` result of the pure function. -/
@[inline] def mulDivErr (d : UInt64) : UInt64 :=
  if d == 0 then LErr.divByZero else Err.arithmeticOverflow

def mulDivFloorM (a b d : UInt64) : SolanaM UInt64 :=
  if d == 0 then SolanaM.fail LErr.divByZero else
  let w := mulWide a b
  if w.1 != 0 && w.1 ≥ d then SolanaM.fail Err.arithmeticOverflow
  else SolanaM.pure (if w.1 == 0 then w.2 / d else div128 w.1 w.2 d)

def mulDivCeilM (a b d : UInt64) : SolanaM UInt64 :=
  if d == 0 then SolanaM.fail LErr.divByZero else
  let w := mulWide a b
  if w.1 != 0 && w.1 ≥ d then SolanaM.fail Err.arithmeticOverflow else
  let q := if w.1 == 0 then w.2 / d else div128 w.1 w.2 d
  let r := w.2 - q * d
  if r == 0 then SolanaM.pure q
  else if q == 0xFFFFFFFFFFFFFFFF then SolanaM.fail Err.arithmeticOverflow
  else SolanaM.pure (q + 1)

@[inline] def mulDivM (r : Rounding) (a b d : UInt64) : SolanaM UInt64 :=
  match r with
  | .floor => mulDivFloorM a b d
  | .ceil => mulDivCeilM a b d

/-! ### Proofs -/

private theorem toNat_eq_zero_iff (x : UInt64) : x = 0 ↔ x.toNat = 0 := by
  constructor
  · intro h; subst h; rfl
  · intro h; exact UInt64.toNat_inj.mp (by rw [h]; rfl)

/-- The two words of `mulWide` and the 64-bit fit condition. -/
private theorem wide_facts (a b d : UInt64) (hd : d.toNat ≠ 0) :
    a.toNat * b.toNat = (mulWide a b).1.toNat * 2^64 + (mulWide a b).2.toNat ∧
    ((mulWide a b).1.toNat < d.toNat ↔ a.toNat * b.toNat / d.toNat < 2^64) := by
  have hs := mulWide_spec a b
  have hlo := (mulWide a b).2.toNat_lt
  refine ⟨hs.symm, ?_⟩
  rw [Nat.div_lt_iff_lt_mul (by omega), ← hs]
  constructor <;> intro h <;> omega

/-- Quotient/remainder used by both roundings: exact Euclidean division of `a*b` by `d`,
    whenever the quotient fits. -/
private theorem qr_spec (a b d : UInt64) (hd : d.toNat ≠ 0)
    (hfit : (mulWide a b).1 = 0 ∨ (mulWide a b).1.toNat < d.toNat) :
    (if (mulWide a b).1 = 0 then (mulWide a b).2 / d
      else div128 (mulWide a b).1 (mulWide a b).2 d).toNat = a.toNat * b.toNat / d.toNat ∧
    ((mulWide a b).2 - (if (mulWide a b).1 = 0 then (mulWide a b).2 / d
      else div128 (mulWide a b).1 (mulWide a b).2 d) * d).toNat = a.toNat * b.toNat % d.toNat := by
  obtain ⟨hab, _⟩ := wide_facts a b d hd
  by_cases h0 : (mulWide a b).1 = 0
  · have hw1 : (mulWide a b).1.toNat = 0 := by rw [h0]; rfl
    simp only [h0, if_true]
    rw [hab, hw1, Nat.zero_mul, Nat.zero_add]
    refine ⟨by rw [UInt64.toNat_div], ?_⟩
    generalize (mulWide a b).2 = L
    rw [UInt64.toNat_sub, UInt64.toNat_mul, UInt64.toNat_div]
    have hL := L.toNat_lt
    have h1 := Nat.div_add_mod L.toNat d.toNat
    have h2 : L.toNat / d.toNat * d.toNat ≤ L.toNat := Nat.div_mul_le_self _ _
    rw [Nat.mod_eq_of_lt (by omega : L.toNat / d.toNat * d.toNat < 2^64)]
    rw [Nat.mul_comm] at h1
    omega
  · have hlt : (mulWide a b).1.toNat < d.toNat := hfit.resolve_left h0
    simp only [h0, if_false]
    rw [hab]
    exact div128_spec _ _ d hlt

theorem mulDivFloor_spec (a b d q : UInt64) :
    mulDivFloor a b d = some q ↔
      d.toNat ≠ 0 ∧ a.toNat * b.toNat / d.toNat < 2^64 ∧ q.toNat = a.toNat * b.toNat / d.toNat := by
  unfold mulDivFloor
  by_cases hd : d = 0
  · subst hd; simp
  have hdn : d.toNat ≠ 0 := fun h => hd ((toNat_eq_zero_iff d).mpr h)
  obtain ⟨hab, hfitIff⟩ := wide_facts a b d hdn
  simp only [beq_iff_eq, hd, if_false]
  by_cases h0 : (mulWide a b).1 = 0
  · have hw1 : (mulWide a b).1.toNat = 0 := by rw [h0]; rfl
    simp only [h0, if_true, Option.some.injEq]
    have hfit : a.toNat * b.toNat / d.toNat < 2^64 := hfitIff.mp (by omega)
    constructor
    · intro h; subst h; refine ⟨hdn, hfit, ?_⟩; rw [UInt64.toNat_div, hab, hw1]; simp
    · rintro ⟨_, _, hq⟩; apply UInt64.toNat_inj.mp; rw [hq, UInt64.toNat_div, hab, hw1]; simp
  · simp only [h0, if_false]
    by_cases hge : (mulWide a b).1 ≥ d
    · simp only [hge, if_true]
      have : ¬ a.toNat * b.toNat / d.toNat < 2^64 := by
        rw [← hfitIff]; rw [GE.ge, UInt64.le_iff_toNat_le] at hge; omega
      simp [this]
    · simp only [hge, if_false, Option.some.injEq]
      have hlt : (mulWide a b).1.toNat < d.toNat := by
        rw [GE.ge, UInt64.le_iff_toNat_le] at hge; omega
      obtain ⟨hq, _⟩ := div128_spec (mulWide a b).1 (mulWide a b).2 d hlt
      rw [← hab] at hq
      constructor
      · intro h; subst h; exact ⟨hdn, hfitIff.mp hlt, hq⟩
      · rintro ⟨_, _, hq'⟩; apply UInt64.toNat_inj.mp; rw [hq, hq']

namespace Spec
/-- `⌈x / d⌉` on naturals (specification only). -/
def ceilDiv (x d : Nat) : Nat := (x + d - 1) / d
end Spec
open Spec

private theorem ceilDiv_eq (x d : Nat) (hd : 0 < d) :
    ceilDiv x d = if x % d = 0 then x / d else x / d + 1 := by
  unfold ceilDiv
  have h := Nat.div_add_mod x d
  split
  · rename_i hm
    have hx : x = d * (x / d) := by omega
    conv => lhs; rw [hx]
    rw [show d * (x / d) + d - 1 = (d - 1) + (x / d) * d by rw [Nat.mul_comm]; omega,
      Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt (by omega)]; omega
  · rename_i hm
    have hx : x + d - 1 = (x % d - 1) + (x / d + 1) * d := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega
    rw [hx, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt (by have := Nat.mod_lt x hd; omega)]
    omega

theorem mulDivCeil_spec (a b d q : UInt64) :
    mulDivCeil a b d = some q ↔
      d.toNat ≠ 0 ∧ ceilDiv (a.toNat * b.toNat) d.toNat < 2^64 ∧
        q.toNat = ceilDiv (a.toNat * b.toNat) d.toNat := by
  unfold mulDivCeil
  by_cases hd : d = 0
  · subst hd; simp
  have hdn : d.toNat ≠ 0 := fun h => hd ((toNat_eq_zero_iff d).mpr h)
  have hdpos : 0 < d.toNat := by omega
  obtain ⟨hab, hfitIff⟩ := wide_facts a b d hdn
  rw [ceilDiv_eq _ _ hdpos]
  simp only [beq_iff_eq, hd, if_false]
  by_cases hbig : ((mulWide a b).1 != 0 && (mulWide a b).1 ≥ d) = true
  · simp only [hbig, if_true]
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hbig
    have hge := hbig.2; rw [GE.ge, UInt64.le_iff_toNat_le] at hge
    have hnf : ¬ a.toNat * b.toNat / d.toNat < 2^64 := by rw [← hfitIff]; omega
    have : ¬ (if a.toNat * b.toNat % d.toNat = 0 then a.toNat * b.toNat / d.toNat
        else a.toNat * b.toNat / d.toNat + 1) < 2^64 := by split <;> omega
    simp [this]
  · have hbig' : ((mulWide a b).1 != 0 && (mulWide a b).1 ≥ d) = false := by simpa using hbig
    simp only [hbig', Bool.false_eq_true, if_false]
    have hfit : (mulWide a b).1 = 0 ∨ (mulWide a b).1.toNat < d.toNat := by
      simp only [Bool.and_eq_false_iff, bne_eq_false_iff_eq, decide_eq_false_iff_not] at hbig'
      rcases hbig' with h | h
      · exact Or.inl h
      · right; rw [GE.ge, UInt64.le_iff_toNat_le] at h; omega
    obtain ⟨hq, hr⟩ := qr_spec a b d hdn hfit
    generalize (if (mulWide a b).1 = 0 then (mulWide a b).2 / d
      else div128 (mulWide a b).1 (mulWide a b).2 d) = q0 at hq hr ⊢
    generalize hrr : (mulWide a b).2 - q0 * d = r0 at hr ⊢
    have hqlt := q0.toNat_lt
    by_cases hr0 : r0 = 0
    · have hm : a.toNat * b.toNat % d.toNat = 0 := by rw [← hr, hr0]; rfl
      simp only [hr0, if_true, hm, Option.some.injEq]
      constructor
      · intro h; subst h; exact ⟨hdn, by omega, hq⟩
      · rintro ⟨_, _, h⟩; exact UInt64.toNat_inj.mp (by rw [h, hq])
    · have hm : a.toNat * b.toNat % d.toNat ≠ 0 := by
        intro h; apply hr0; apply UInt64.toNat_inj.mp; rw [hr, h]; rfl
      simp only [hr0, if_false, hm]
      by_cases hmax : q0 = 0xFFFFFFFFFFFFFFFF
      · have : q0.toNat = 2^64 - 1 := by rw [hmax]; rfl
        simp only [hmax, if_true]
        simp; omega
      · have hne : q0.toNat ≠ 2^64 - 1 := by
          intro h; apply hmax; apply UInt64.toNat_inj.mp; rw [h]; rfl
        simp only [hmax, if_false, Option.some.injEq]
        have hadd : (q0 + 1).toNat = q0.toNat + 1 := by
          rw [UInt64.toNat_add]; show (q0.toNat + 1) % 2^64 = _; omega
        constructor
        · intro h; subst h; refine ⟨hdn, by omega, by rw [hadd, hq]⟩
        · rintro ⟨_, _, h⟩; exact UInt64.toNat_inj.mp (by rw [h, hadd, hq])

/-! ### On-chain versions agree with the pure functions -/

theorem mulDivFloorM_eq (a b d : UInt64) (s : SvmState) :
    mulDivFloorM a b d s =
      match mulDivFloor a b d with
      | some q => .ok q s
      | none => .err (mulDivErr d) s := by
  unfold mulDivFloorM mulDivFloor mulDivErr
  by_cases hd : d = 0
  · subst hd; rfl
  simp only [beq_iff_eq, hd, if_false]
  by_cases h0 : (mulWide a b).1 = 0
  · simp [h0, SolanaM.pure]
  · by_cases hge : (mulWide a b).1 ≥ d
    · simp [h0, hge, SolanaM.fail]
    · simp [h0, hge, SolanaM.pure]

theorem mulDivCeilM_eq (a b d : UInt64) (s : SvmState) :
    mulDivCeilM a b d s =
      match mulDivCeil a b d with
      | some q => .ok q s
      | none => .err (mulDivErr d) s := by
  unfold mulDivCeilM mulDivCeil mulDivErr
  by_cases hd : d = 0
  · subst hd; rfl
  simp only [beq_iff_eq, hd, if_false]
  by_cases hbig : ((mulWide a b).1 != 0 && (mulWide a b).1 ≥ d) = true
  · simp only [hbig, if_true]; rfl
  · have hb : ((mulWide a b).1 != 0 && (mulWide a b).1 ≥ d) = false := by simpa using hbig
    simp only [hb, Bool.false_eq_true, if_false]
    generalize (if (mulWide a b).1 = 0 then (mulWide a b).2 / d
      else div128 (mulWide a b).1 (mulWide a b).2 d) = q
    by_cases hr : (mulWide a b).2 - q * d = 0
    · simp [hr, SolanaM.pure]
    · by_cases hm : q = 0xFFFFFFFFFFFFFFFF
      · subst hm; simp [hr, SolanaM.fail]
      · simp [hr, hm, SolanaM.pure]

/-- On-chain `mulDivFloorM` succeeds with `q` iff the exact floor is defined, fits, and equals `q`. -/
theorem mulDivFloorM_ok_iff (a b d q : UInt64) (s s' : SvmState) :
    (∃ h : mulDivFloorM a b d s = .ok q s', True) ↔
      s' = s ∧ d.toNat ≠ 0 ∧ a.toNat * b.toNat / d.toNat < 2^64 ∧
        q.toNat = a.toNat * b.toNat / d.toNat := by
  rw [mulDivFloorM_eq, ← mulDivFloor_spec]
  cases h : mulDivFloor a b d with
  | none => simp
  | some q' =>
    simp only [Option.some.injEq]
    constructor
    · rintro ⟨h, -⟩; cases h; exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, trivial⟩

/-- On-chain `mulDivCeilM` succeeds with `q` iff the exact ceiling is defined, fits, and equals `q`. -/
theorem mulDivCeilM_ok_iff (a b d q : UInt64) (s s' : SvmState) :
    (∃ h : mulDivCeilM a b d s = .ok q s', True) ↔
      s' = s ∧ d.toNat ≠ 0 ∧ ceilDiv (a.toNat * b.toNat) d.toNat < 2^64 ∧
        q.toNat = ceilDiv (a.toNat * b.toNat) d.toNat := by
  rw [mulDivCeilM_eq, ← mulDivCeil_spec]
  cases h : mulDivCeil a b d with
  | none => simp
  | some q' =>
    simp only [Option.some.injEq]
    constructor
    · rintro ⟨h, -⟩; cases h; exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, trivial⟩

end Lemma.Math
