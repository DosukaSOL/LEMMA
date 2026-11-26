/-
  Lemma.Compiler.NatLowering — kernel-checked correctness of the instruction sequences that
  LEMMA patch 0001 emits for `Nat` operations.

  Scope (read carefully): these theorems prove that each *check-and-compute scheme* computes
  Lean's `Nat` result exactly whenever it does not abort, and aborts exactly when the true
  result does not fit in 64 bits. They are stated over `UInt64` (the register semantics of
  `add64`/`mul64`/`sub64`/`div64`/`mod64`, which wrap modulo 2^64 like Lean's `UInt64`).
  They do NOT prove that `Lower.lean` emits these schemes (that is checked by tests in
  `tests/LemmaTest/NatTests.lean` and by code review of the patch), nor anything about
  later compiler passes.
-/

namespace Lemma.Compiler.NatLowering

/-- `Nat.add` scheme: `r := a + b (mod 2^64)`; abort iff `r < a`. -/
theorem add_abort_iff (a b : UInt64) :
    (a + b < a) ↔ 2 ^ 64 ≤ a.toNat + b.toNat := by
  have ha := a.toNat_lt; have hb := b.toNat_lt
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
  constructor
  · intro h
    rcases Nat.lt_or_ge (a.toNat + b.toNat) (2 ^ 64) with hc | hc
    · rw [Nat.mod_eq_of_lt hc] at h; omega
    · exact hc
  · intro h
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    omega

theorem add_exact (a b : UInt64) (h : ¬ (a + b < a)) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [add_abort_iff] at h
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]

/-- `Nat.mul` scheme: `r := a * b (mod 2^64)`; if `a = 0` the result is exact, otherwise abort
    iff `r / a ≠ b`. -/
theorem mul_abort_iff (a b : UInt64) (ha0 : a ≠ 0) :
    ((a * b) / a ≠ b) ↔ 2 ^ 64 ≤ a.toNat * b.toNat := by
  have ha := a.toNat_lt; have hb := b.toNat_lt
  have hapos : 0 < a.toNat := by
    rcases Nat.eq_zero_or_pos a.toNat with h | h
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) ha0
    · exact h
  rw [ne_eq, ← UInt64.toNat_inj, UInt64.toNat_div, UInt64.toNat_mul]
  constructor
  · intro h
    rcases Nat.lt_or_ge (a.toNat * b.toNat) (2 ^ 64) with hc | hc
    · rw [Nat.mod_eq_of_lt hc, Nat.mul_div_cancel_left _ hapos] at h
      exact absurd rfl h
    · exact hc
  · intro h heq
    have hlt : a.toNat * b.toNat % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
    have : a.toNat * (a.toNat * b.toNat % 2 ^ 64 / a.toNat) ≤ a.toNat * b.toNat % 2 ^ 64 :=
      Nat.mul_div_le _ _
    rw [heq] at this
    omega

theorem mul_exact_of_zero (b : UInt64) : ((0 : UInt64) * b).toNat = (0 : UInt64).toNat * b.toNat := by
  simp

theorem mul_exact (a b : UInt64) (ha0 : a ≠ 0) (h : ¬ ((a * b) / a ≠ b)) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [mul_abort_iff a b ha0] at h
  rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (by omega)]

/-- `Nat.sub` scheme: `if a < b then 0 else a - b` equals truncated subtraction. -/
theorem sub_exact (a b : UInt64) :
    (if a < b then 0 else (a - b).toNat) = a.toNat - b.toNat := by
  split
  · rename_i h; rw [UInt64.lt_iff_toNat_lt] at h; omega
  · rename_i h; rw [UInt64.lt_iff_toNat_lt] at h
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]

/-- `Nat.div` scheme: `if b = 0 then 0 else a / b` (no divide-by-zero trap). -/
theorem div_exact (a b : UInt64) :
    (if b = 0 then 0 else (a / b).toNat) = a.toNat / b.toNat := by
  split
  · rename_i h; subst h; simp
  · rw [UInt64.toNat_div]

/-- `Nat.mod` scheme: `if b = 0 then a else a % b`. -/
theorem mod_exact (a b : UInt64) :
    (if b = 0 then a.toNat else (a % b).toNat) = a.toNat % b.toNat := by
  split
  · rename_i h; subst h; simp
  · rw [UInt64.toNat_mod]

/-- `UInt32.ofNatClamp` (formerly `ofNatTruncate`) scheme on an exact register value `v`:
    clamp to `2^32 - 1`. -/
theorem trunc32_exact (v : UInt64) :
    (if v > 0xFFFFFFFF then (0xFFFFFFFF : UInt64) else v).toNat =
      (UInt32.ofNatClamp v.toNat).toNat := by
  have hc : (UInt32.ofNatClamp v.toNat).toNat = min v.toNat (2 ^ 32 - 1) :=
    BitVec.toNat_ofNatClamp
  rw [hc]
  by_cases h : v > 0xFFFFFFFF
  · simp only [h, ↓reduceIte]; rw [GT.gt, UInt64.lt_iff_toNat_lt] at h; simp at h ⊢; omega
  · simp only [h, ↓reduceIte]; rw [GT.gt, UInt64.lt_iff_toNat_lt] at h; simp at h ⊢; omega

end Lemma.Compiler.NatLowering
