/-
  Lemma.Math.ConstantProduct — constant-product (x·y = k) swap quote, proven on the on-chain
  function itself.

  `swapOutM reserveIn reserveOut amountIn feeBps` computes
      inAfterFee = ⌊amountIn · (10000 − feeBps) / 10000⌋        (floor: fee rounds up, pool's favour)
      out        = ⌊reserveOut · inAfterFee / (reserveIn + inAfterFee)⌋   (floor: pool's favour)

  Proven (for every input on which it succeeds):
  * `swapOutM_k_nondecreasing`: (reserveIn + amountIn) · (reserveOut − out) ≥ reserveIn · reserveOut
  * `swapOutM_lt_reserve`: out < reserveOut whenever reserveIn > 0
  * `swapOutM_rounds_for_pool`: out · (reserveIn + inAfterFee) ≤ reserveOut · inAfterFee
    (the trader never receives more than the exact real-valued quote)
  * `swapOutM_fee_rounds_for_pool`: inAfterFee · 10000 ≤ amountIn · (10000 − feeBps)
-/
import Lemma.Math.MulDiv

namespace Lemma.Math
open LeanSVM

/-- Fee denominator: fees are expressed in basis points. -/
abbrev bpsDenom : UInt64 := 10000

/-- Amount credited to the curve after the fee is taken (fee rounds in the pool's favour). -/
def inAfterFeeM (amountIn feeBps : UInt64) : SolanaM UInt64 :=
  if feeBps > bpsDenom then SolanaM.fail Err.invalidArgument
  else mulDivFloorM amountIn (bpsDenom - feeBps) bpsDenom

/-- Constant-product output quote. Fails (never wraps) on invalid fee, overflow, or an empty pool. -/
def swapOutM (reserveIn reserveOut amountIn feeBps : UInt64) : SolanaM UInt64 :=
  SolanaM.bind (inAfterFeeM amountIn feeBps) fun aif =>
  SolanaM.bind (checkedAdd64 reserveIn aif) fun denom =>
  mulDivFloorM reserveOut aif denom

/-! ### Proofs -/

private theorem toNat_bps : bpsDenom.toNat = 10000 := rfl

/-- Characterisation of a successful run. -/
theorem swapOutM_ok (x y amt fee out : UInt64) (s s' : SvmState)
    (h : swapOutM x y amt fee s = .ok out s') :
    ∃ aif : UInt64,
      s' = s ∧ fee.toNat ≤ 10000 ∧
      aif.toNat = amt.toNat * (10000 - fee.toNat) / 10000 ∧
      x.toNat + aif.toNat < 2^64 ∧ x.toNat + aif.toNat ≠ 0 ∧
      out.toNat = y.toNat * aif.toNat / (x.toNat + aif.toNat) := by
  unfold swapOutM SolanaM.bind at h
  -- fee step
  unfold inAfterFeeM at h
  by_cases hf : fee > bpsDenom
  · simp [hf, SolanaM.fail] at h
  simp only [hf, ite_false] at h
  have hfee : fee.toNat ≤ 10000 := by
    rw [GT.gt, UInt64.lt_iff_toNat_lt, toNat_bps] at hf; omega
  have hsub : (bpsDenom - fee).toNat = 10000 - fee.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, toNat_bps]; exact hfee), toNat_bps]
  split at h
  · rename_i aif s1 h1
    obtain ⟨rfl, -, -, haif⟩ :=
      (mulDivFloorM_ok_iff amt (bpsDenom - fee) bpsDenom aif s s1).mp h1
    rw [hsub, toNat_bps] at haif
    -- checked add step
    unfold checkedAdd64 at h
    simp only [Bind.bind, SolanaM.bind, SolanaM.require, Pure.pure, SolanaM.pure] at h
    by_cases hov : x + aif ≥ x
    · simp only [hov, decide_true, ite_true] at h
      have hno : x.toNat + aif.toNat < 2^64 := by
        rw [GE.ge, UInt64.le_iff_toNat_le, UInt64.toNat_add] at hov
        have := x.toNat_lt; have := aif.toNat_lt
        rcases Nat.lt_or_ge (x.toNat + aif.toNat) (2^64) with h' | h'
        · exact h'
        · exfalso; rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (by omega)] at hov; omega
      have hadd : (x + aif).toNat = x.toNat + aif.toNat := by
        rw [UInt64.toNat_add, Nat.mod_eq_of_lt hno]
      obtain ⟨rfl, hd, -, hout⟩ := (mulDivFloorM_ok_iff y aif (x + aif) out _ s').mp h
      rw [hadd] at hd hout
      exact ⟨aif, rfl, hfee, haif, hno, hd, hout⟩
    · simp [hov, SolanaM.fail] at h
  · simp at h

theorem swapOutM_fee_rounds_for_pool (x y amt fee out : UInt64) (s s' : SvmState)
    (h : swapOutM x y amt fee s = .ok out s') :
    ∃ aif : UInt64, aif.toNat * 10000 ≤ amt.toNat * (10000 - fee.toNat) ∧
      aif.toNat ≤ amt.toNat := by
  obtain ⟨aif, -, hfee, haif, -⟩ := swapOutM_ok x y amt fee out s s' h
  refine ⟨aif, ?_, ?_⟩
  · rw [haif]; exact Nat.div_mul_le_self _ _
  · rw [haif, Nat.div_le_iff_le_mul_add_pred (by decide)]
    have : amt.toNat * (10000 - fee.toNat) ≤ amt.toNat * 10000 := Nat.mul_le_mul_left _ (by omega)
    omega

theorem swapOutM_rounds_for_pool (x y amt fee out : UInt64) (s s' : SvmState)
    (h : swapOutM x y amt fee s = .ok out s') :
    ∃ aif : UInt64, out.toNat * (x.toNat + aif.toNat) ≤ y.toNat * aif.toNat := by
  obtain ⟨aif, -, -, -, -, -, hout⟩ := swapOutM_ok x y amt fee out s s' h
  exact ⟨aif, by rw [hout]; exact Nat.div_mul_le_self _ _⟩

theorem swapOutM_lt_reserve (x y amt fee out : UInt64) (s s' : SvmState)
    (h : swapOutM x y amt fee s = .ok out s') (hx : 0 < x.toNat) :
    out.toNat < y.toNat ∨ y.toNat = 0 := by
  obtain ⟨aif, -, -, -, -, hd, hout⟩ := swapOutM_ok x y amt fee out s s' h
  rcases Nat.eq_zero_or_pos y.toNat with hy | hy
  · exact Or.inr hy
  left
  rw [hout, Nat.div_lt_iff_lt_mul (by omega)]
  -- y·aif < y·(x + aif) because x > 0 and y > 0
  exact (Nat.mul_lt_mul_left hy).mpr (by omega)

theorem swapOutM_k_nondecreasing (x y amt fee out : UInt64) (s s' : SvmState)
    (h : swapOutM x y amt fee s = .ok out s') :
    (x.toNat + amt.toNat) * (y.toNat - out.toNat) ≥ x.toNat * y.toNat := by
  obtain ⟨aif, -, hfee, haif, -, hd, hout⟩ := swapOutM_ok x y amt fee out s s' h
  have haifle : aif.toNat ≤ amt.toNat := by
    rw [haif, Nat.div_le_iff_le_mul_add_pred (by decide)]
    have : amt.toNat * (10000 - fee.toNat) ≤ amt.toNat * 10000 := Nat.mul_le_mul_left _ (by omega)
    omega
  generalize hX : x.toNat = X at *
  generalize hY : y.toNat = Y at *
  generalize hA : aif.toNat = A at *
  generalize hO : out.toNat = O at *
  -- O·(X+A) ≤ Y·A   (floor)
  have hfl : O * (X + A) ≤ Y * A := by rw [hout]; exact Nat.div_mul_le_self _ _
  -- O ≤ Y
  have hOY : O ≤ Y := by
    rw [hout]; apply Nat.div_le_of_le_mul
    calc Y * A ≤ Y * (X + A) := Nat.mul_le_mul_left _ (by omega)
      _ = (X + A) * Y := Nat.mul_comm _ _
  -- (X + A)·(Y − O) = (X+A)·Y − (X+A)·O ≥ (X+A)·Y − Y·A = X·Y
  have h1 : (X + A) * (Y - O) ≥ X * Y := by
    rw [Nat.mul_sub]
    have e1 : (X + A) * Y = X * Y + Y * A := by rw [Nat.add_mul, Nat.mul_comm A Y]
    have e2 : (X + A) * O = O * (X + A) := Nat.mul_comm _ _
    omega
  exact Nat.le_trans h1 (Nat.mul_le_mul_right _ (by omega))

end Lemma.Math
