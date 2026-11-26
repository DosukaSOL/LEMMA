/-
  Lemma.Math.Wide — exact 128-bit intermediate arithmetic in pure `UInt64`.

  * `mulWide a b = (hi, lo)` with `hi * 2^64 + lo = a * b` (proved: `mulWide_spec`).
  * `div128 hi lo d = (q, r)` with `q = ⌊(hi·2^64 + lo) / d⌋` and `r` the remainder, when
    `hi < d` (proved: `div128_spec`).

  Runtime code here uses only `UInt64` operations; `Nat` appears only in proofs. All theorems are
  kernel-checked with the standard axioms (no `bv_decide` / `native_decide`).
-/

namespace Lemma.Math

def M32 : UInt64 := 0xFFFFFFFF

/-- 64×64 → 128-bit multiply, returned as `(hi, lo)`. Pure `UInt64`, no `Nat` at runtime. -/
@[inline] def mulWide (a b : UInt64) : UInt64 × UInt64 :=
  let a0 := a &&& M32
  let a1 := a >>> 32
  let b0 := b &&& M32
  let b1 := b >>> 32
  let p00 := a0 * b0
  let p01 := a0 * b1
  let p10 := a1 * b0
  let p11 := a1 * b1
  let mid := (p00 >>> 32) + (p01 &&& M32) + (p10 &&& M32)
  let lo := (p00 &&& M32) + (mid <<< 32)
  let hi := p11 + (p01 >>> 32) + (p10 >>> 32) + (mid >>> 32)
  (hi, lo)

theorem toNat_and_M32 (x : UInt64) : (x &&& M32).toNat = x.toNat % 2 ^ 32 := by
  rw [UInt64.toNat_and]; show x.toNat &&& (2^32 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]

theorem toNat_shr32 (x : UInt64) : (x >>> 32).toNat = x.toNat / 2 ^ 32 := by
  rw [UInt64.toNat_shiftRight]; exact Nat.shiftRight_eq_div_pow _ _

theorem toNat_shl32 (x : UInt64) : (x <<< 32).toNat = (x.toNat % 2 ^ 32) * 2 ^ 32 := by
  rw [UInt64.toNat_shiftLeft]; show (x.toNat <<< 32) % 2^64 = _
  rw [Nat.shiftLeft_eq, show (2:Nat)^64 = 2^32 * 2^32 by rfl, Nat.mul_mod_mul_right]

theorem toNat_add_of_lt (x y : UInt64) (h : x.toNat + y.toNat < 2 ^ 64) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]

theorem mulWide_spec (a b : UInt64) :
    (mulWide a b).1.toNat * 2 ^ 64 + (mulWide a b).2.toNat = a.toNat * b.toNat := by
  have ha := a.toNat_lt; have hb := b.toNat_lt
  simp only [mulWide]
  -- decompose into 32-bit halves
  have hm0 : ∀ x y : Nat, x < 2^32 → y < 2^32 → x * y < 2^64 := fun x y hx hy => by
    have := Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_of_lt hy) (by omega); simpa using this
  have hmul : ∀ x y : UInt64, x.toNat < 2^32 → y.toNat < 2^32 → (x * y).toNat = x.toNat * y.toNat :=
    fun x y hx hy => by rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (hm0 _ _ hx hy)]
  have ha0 : (a &&& M32).toNat < 2^32 := by rw [toNat_and_M32]; omega
  have hb0 : (b &&& M32).toNat < 2^32 := by rw [toNat_and_M32]; omega
  have ha1 : (a >>> 32).toNat < 2^32 := by rw [toNat_shr32]; omega
  have hb1 : (b >>> 32).toNat < 2^32 := by rw [toNat_shr32]; omega
  rw [toNat_and_M32] at ha0 hb0; rw [toNat_shr32] at ha1 hb1
  generalize hA0 : a.toNat % 2^32 = A0 at *
  generalize hA1 : a.toNat / 2^32 = A1 at *
  generalize hB0 : b.toNat % 2^32 = B0 at *
  generalize hB1 : b.toNat / 2^32 = B1 at *
  have hAd : a.toNat = A1 * 2^32 + A0 := by omega
  have hBd : b.toNat = B1 * 2^32 + B0 := by omega
  have key : a.toNat * b.toNat = (A1*B1) * 2^64 + (A0*B1 + A1*B0) * 2^32 + A0*B0 := by
    rw [hAd, hBd, show (2:Nat)^64 = 2^32 * 2^32 from rfl]
    generalize (2:Nat)^32 = K
    simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
    omega
  have e00 : ((a &&& M32) * (b &&& M32)).toNat = A0 * B0 := by
    rw [hmul _ _ (by rw [toNat_and_M32]; omega) (by rw [toNat_and_M32]; omega), toNat_and_M32,
      toNat_and_M32, hA0, hB0]
  have e01 : ((a &&& M32) * (b >>> 32)).toNat = A0 * B1 := by
    rw [hmul _ _ (by rw [toNat_and_M32]; omega) (by rw [toNat_shr32]; omega), toNat_and_M32,
      toNat_shr32, hA0, hB1]
  have e10 : ((a >>> 32) * (b &&& M32)).toNat = A1 * B0 := by
    rw [hmul _ _ (by rw [toNat_shr32]; omega) (by rw [toNat_and_M32]; omega), toNat_shr32,
      toNat_and_M32, hA1, hB0]
  have e11 : ((a >>> 32) * (b >>> 32)).toNat = A1 * B1 := by
    rw [hmul _ _ (by rw [toNat_shr32]; omega) (by rw [toNat_shr32]; omega), toNat_shr32,
      toNat_shr32, hA1, hB1]
  have b00 := hm0 _ _ ha0 hb0; have b01 := hm0 _ _ ha0 hb1
  have b10 := hm0 _ _ ha1 hb0; have b11 := hm0 _ _ ha1 hb1
  generalize (a &&& M32) * (b &&& M32) = p00 at *
  generalize (a &&& M32) * (b >>> 32) = p01 at *
  generalize (a >>> 32) * (b &&& M32) = p10 at *
  generalize (a >>> 32) * (b >>> 32) = p11 at *
  generalize A0 * B0 = P00 at *
  generalize A0 * B1 = P01 at *
  generalize A1 * B0 = P10 at *
  generalize A1 * B1 = P11 at *
  have habAB : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 :=
    Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (by omega)
  -- mid (no overflow: < 3 * 2^32)
  have m1 : ((p00 >>> 32) + (p01 &&& M32)).toNat = P00 / 2^32 + P01 % 2^32 := by
    rw [toNat_add_of_lt] <;> simp only [toNat_shr32, toNat_and_M32, e00, e01] <;> omega
  have emid : ((p00 >>> 32) + (p01 &&& M32) + (p10 &&& M32)).toNat =
      P00 / 2^32 + P01 % 2^32 + P10 % 2^32 := by
    rw [toNat_add_of_lt, m1, toNat_and_M32, e10]; rw [m1, toNat_and_M32, e10]; omega
  generalize (p00 >>> 32) + (p01 &&& M32) + (p10 &&& M32) = mid at *
  have elo : ((p00 &&& M32) + (mid <<< 32)).toNat = P00 % 2^32 + (mid.toNat % 2^32) * 2^32 := by
    rw [toNat_add_of_lt] <;> simp only [toNat_shl32, toNat_and_M32, e00] <;> omega
  -- the true high word is < 2^64 because a*b < 2^128; every partial sum is below it
  have hhi : P11 + P01 / 2^32 + P10 / 2^32 + mid.toNat / 2^32 < 2^64 := by omega
  have h1 : (p11 + (p01 >>> 32)).toNat = P11 + P01 / 2^32 := by
    rw [toNat_add_of_lt] <;> simp only [toNat_shr32, e11, e01] <;> omega
  have h2 : (p11 + (p01 >>> 32) + (p10 >>> 32)).toNat = P11 + P01 / 2^32 + P10 / 2^32 := by
    rw [toNat_add_of_lt, h1, toNat_shr32, e10]; rw [h1, toNat_shr32, e10]; omega
  have ehi : (p11 + (p01 >>> 32) + (p10 >>> 32) + (mid >>> 32)).toNat =
      P11 + P01 / 2^32 + P10 / 2^32 + mid.toNat / 2^32 := by
    rw [toNat_add_of_lt, h2, toNat_shr32]; rw [h2, toNat_shr32]; omega
  rw [elo, ehi]
  omega

namespace Spec
/-- Reference long division returning `(quotient, remainder)`. One step per remaining bit of
    `lo` (MSB first). `rem < d` is the running remainder; `rem >>> 63` detects that
    `2*rem + bit` overflowed 64 bits (then it is ≥ d). Proof device; the runtime loop
    `div128Loop` computes the same quotient without carrying a pair. -/
def div128LoopQR (d rem lo q steps : UInt64) : UInt64 × UInt64 :=
  if h : steps = 0 then (q, rem) else
    let top := lo >>> 63
    let carry := rem >>> 63
    let rem2 := (rem <<< 1) + top
    if carry != 0 || rem2 ≥ d then
      div128LoopQR d (rem2 - d) (lo <<< 1) ((q <<< 1) + 1) (steps - 1)
    else
      div128LoopQR d rem2 (lo <<< 1) (q <<< 1) (steps - 1)
termination_by steps.toNat
decreasing_by
  all_goals
    have hpos : 0 < steps.toNat := by
      have hne : steps.toNat ≠ 0 := fun hz => h (UInt64.toNat_inj.mp (by rw [hz]; rfl))
      omega
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
    simp; omega

end Spec
open Spec

/-- Runtime long division: identical recursion to `Spec.div128LoopQR`, returning only the
    quotient (the compiler lowers this tail recursion to a loop; a tuple-valued loop exit is
    not supported by lean-svm). -/
def div128Loop (d rem lo q steps : UInt64) : UInt64 :=
  if h : steps = 0 then q else
    let top := lo >>> 63
    let carry := rem >>> 63
    let rem2 := (rem <<< 1) + top
    if carry != 0 || rem2 ≥ d then
      div128Loop d (rem2 - d) (lo <<< 1) ((q <<< 1) + 1) (steps - 1)
    else
      div128Loop d rem2 (lo <<< 1) (q <<< 1) (steps - 1)
termination_by steps.toNat
decreasing_by
  all_goals
    have hpos : 0 < steps.toNat := by
      have hne : steps.toNat ≠ 0 := fun hz => h (UInt64.toNat_inj.mp (by rw [hz]; rfl))
      omega
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
    simp; omega

theorem div128Loop_eq (d : UInt64) : ∀ (n : Nat) (steps rem lo q : UInt64), steps.toNat = n →
    div128Loop d rem lo q steps = (div128LoopQR d rem lo q steps).1 := by
  intro n
  induction n with
  | zero =>
    intro steps rem lo q hs
    have h0 : steps = 0 := UInt64.toNat_inj.mp (by rw [hs]; rfl)
    rw [div128Loop, div128LoopQR, dite_eq_left_iff.mpr (fun h => absurd h0 h),
      dite_eq_left_iff.mpr (fun h => absurd h0 h)]
  | succ n ih =>
    intro steps rem lo q hs
    have hne : steps ≠ 0 := fun h => by subst h; simp at hs
    have hs' : (steps - 1).toNat = n := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by show 1 ≤ _; omega))]
      show steps.toNat - 1 = n; omega
    rw [div128Loop, div128LoopQR, dite_eq_right_iff.mpr (fun h => absurd h hne),
      dite_eq_right_iff.mpr (fun h => absurd h hne)]
    simp only []
    split <;> exact ih _ _ _ _ hs'

theorem shr63 (x : UInt64) : (x >>> 63).toNat = x.toNat / 2 ^ 63 := by
  rw [UInt64.toNat_shiftRight]; exact Nat.shiftRight_eq_div_pow _ _

theorem shl1 (x : UInt64) : (x <<< 1).toNat = (2 * x.toNat) % 2 ^ 64 := by
  rw [UInt64.toNat_shiftLeft]; show (x.toNat <<< 1) % 2^64 = _
  rw [Nat.shiftLeft_eq]; omega

/-- Peeling the top bit off the unprocessed window. `e = 64 - steps`. -/
theorem window_step (L e : Nat) (_hL : L < 2 ^ 64) (he : e ≤ 63) :
    (L / 2 ^ 63) * 2 ^ (63 - e) + ((2 * L) % 2 ^ 64) / 2 ^ (e + 1) = L / 2 ^ e := by
  have h2L : (2 * L) % 2^64 = 2 * (L % 2^63) := by omega
  rw [h2L, show (2:Nat)^(e+1) = 2 * 2^e by rw [Nat.pow_succ, Nat.mul_comm],
    Nat.mul_div_mul_left _ _ (by decide)]
  have hp : (2:Nat)^63 = 2^(63 - e) * 2^e := by rw [← Nat.pow_add]; congr 1; omega
  have hsplit : L = L % 2^63 + (L / 2^63 * 2^(63 - e)) * 2^e := by
    rw [Nat.mul_assoc, ← hp]; omega
  have : L / 2^e = L % 2^63 / 2^e + L / 2^63 * 2^(63 - e) := by
    conv => lhs; rw [hsplit]
    exact Nat.add_mul_div_right _ _ (Nat.two_pow_pos e)
  omega

theorem toNat_one : (1 : UInt64).toNat = 1 := rfl

/-- Remainder update of one step: exact, and the new remainder is again `< d`. -/
theorem step_rem (d rem top : UInt64) (hr : rem.toNat < d.toNat) (ht : top.toNat ≤ 1) :
    let rem2 := (rem <<< 1) + top
    ((rem >>> 63 != 0 || rem2 ≥ d) = true →
        2 * rem.toNat + top.toNat ≥ d.toNat ∧ (rem2 - d).toNat = 2 * rem.toNat + top.toNat - d.toNat) ∧
    ((rem >>> 63 != 0 || rem2 ≥ d) = false → rem2.toNat = 2 * rem.toNat + top.toNat) := by
  intro rem2
  have hd := d.toNat_lt
  have hrem2 : rem2.toNat = (2 * rem.toNat + top.toNat) % 2^64 := by
    show ((rem <<< 1) + top).toNat = _
    rw [UInt64.toNat_add, shl1]; omega
  have hc : (rem >>> 63).toNat = rem.toNat / 2^63 := shr63 rem
  constructor
  · intro hcond
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hcond
    rcases hcond with hcar | hge
    · have hc1 : rem.toNat / 2^63 ≠ 0 := by
        intro h0; apply hcar; apply UInt64.toNat_inj.mp; rw [hc, h0]; rfl
      have hbig : 2 * rem.toNat + top.toNat ≥ 2^64 := by omega
      refine ⟨by omega, ?_⟩
      rw [UInt64.toNat_sub, hrem2]; omega
    · rw [GE.ge, UInt64.le_iff_toNat_le, hrem2] at hge
      have hle : d.toNat ≤ 2 * rem.toNat + top.toNat := by omega
      refine ⟨hle, ?_⟩
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hrem2]; exact hge), hrem2]
      omega
  · intro hcond
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq, decide_eq_false_iff_not] at hcond
    obtain ⟨hcar, hlt⟩ := hcond
    have hc0 : rem.toNat / 2^63 = 0 := by rw [← hc, hcar]; rfl
    rw [hrem2]; omega

theorem div128Loop_spec (d : UInt64) : ∀ (n : Nat) (steps rem lo q : UInt64) (Qt : Nat),
    steps.toNat = n → n ≤ 64 → rem.toNat < d.toNat → q.toNat = Qt % 2^64 →
    ∃ Qo, (div128LoopQR d rem lo q steps).1.toNat = Qo % 2^64 ∧
      (div128LoopQR d rem lo q steps).2.toNat < d.toNat ∧
      Qo * d.toNat + (div128LoopQR d rem lo q steps).2.toNat =
        (Qt * d.toNat + rem.toNat) * 2^n + lo.toNat / 2^(64 - n) := by
  intro n
  induction n with
  | zero =>
    intro steps rem lo q Qt hs _ hr hq
    have h0 : steps = 0 := UInt64.toNat_inj.mp (by rw [hs]; rfl)
    rw [div128LoopQR, dite_eq_left_iff.mpr (fun h => absurd h0 h)]
    refine ⟨Qt, hq, hr, ?_⟩
    have := lo.toNat_lt
    simp; omega
  | succ n ih =>
    intro steps rem lo q Qt hs hn hr hq
    have hne : steps ≠ 0 := fun h => by subst h; simp at hs
    have hs' : (steps - 1).toNat = n := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [toNat_one]; omega)),
        toNat_one]; omega
    have hlo := lo.toNat_lt
    have ht : (lo >>> 63).toNat ≤ 1 := by rw [shr63]; omega
    have hwin := window_step lo.toNat (63 - n) hlo (by omega)
    rw [show 63 - (63 - n) = n by omega, show 63 - n + 1 = 64 - n by omega] at hwin
    rw [← shl1, ← shr63] at hwin
    obtain ⟨hT, hF⟩ := step_rem d rem (lo >>> 63) hr ht
    rw [div128LoopQR, dite_eq_right_iff.mpr (fun h => absurd h hne)]
    simp only []
    split
    · rename_i hcond
      obtain ⟨hge, hsub⟩ := hT hcond
      obtain ⟨Qo, h1, h2, h3⟩ := ih (steps - 1) ((rem <<< 1) + (lo >>> 63) - d) (lo <<< 1)
        ((q <<< 1) + 1) (2 * Qt + 1) hs' (by omega) (by rw [hsub]; omega)
        (by rw [UInt64.toNat_add, shl1, hq, toNat_one]; omega)
      refine ⟨Qo, h1, h2, ?_⟩
      have e : (2 * Qt + 1) * d.toNat + (2 * rem.toNat + (lo >>> 63).toNat - d.toNat) =
          2 * (Qt * d.toNat + rem.toNat) + (lo >>> 63).toNat := by
        rw [Nat.add_mul, Nat.mul_assoc]; omega
      rw [h3, hsub, e, show 64 - (n+1) = 63 - n by omega]
      generalize Qt * d.toNat + rem.toNat = X at *
      have a1 : (2 * X + (lo >>> 63).toNat) * 2^n = 2 * (X * 2^n) + (lo >>> 63).toNat * 2^n := by
        rw [Nat.add_mul, Nat.mul_assoc]
      have a2 : X * 2^(n+1) = 2 * (X * 2^n) := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm]
      omega
    · rename_i hcond
      have hcond' : (rem >>> 63 != 0 || (rem <<< 1) + (lo >>> 63) ≥ d) = false := by
        simpa using hcond
      have hadd := hF hcond'
      have hlt : ((rem <<< 1) + (lo >>> 63)).toNat < d.toNat := by
        simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq, decide_eq_false_iff_not] at hcond'
        have := hcond'.2; rw [GE.ge, UInt64.le_iff_toNat_le] at this; omega
      obtain ⟨Qo, h1, h2, h3⟩ := ih (steps - 1) ((rem <<< 1) + (lo >>> 63)) (lo <<< 1)
        (q <<< 1) (2 * Qt) hs' (by omega) hlt (by rw [shl1, hq]; omega)
      refine ⟨Qo, h1, h2, ?_⟩
      have e : 2 * Qt * d.toNat + (2 * rem.toNat + (lo >>> 63).toNat) =
          2 * (Qt * d.toNat + rem.toNat) + (lo >>> 63).toNat := by
        rw [Nat.mul_assoc]; omega
      rw [h3, hadd, e, show 64 - (n+1) = 63 - n by omega]
      generalize Qt * d.toNat + rem.toNat = X at *
      have a1 : (2 * X + (lo >>> 63).toNat) * 2^n = 2 * (X * 2^n) + (lo >>> 63).toNat * 2^n := by
        rw [Nat.add_mul, Nat.mul_assoc]
      have a2 : X * 2^(n+1) = 2 * (X * 2^n) := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm]
      omega

/-- `⌊(hi·2^64 + lo) / d⌋` by 64 restoring long-division steps.
    Meaningful when `hi < d` (so the quotient fits in 64 bits). -/
@[inline] def div128 (hi lo d : UInt64) : UInt64 :=
  div128Loop d hi lo 0 64

theorem div128_spec (hi lo d : UInt64) (hlt : hi.toNat < d.toNat) :
    (div128 hi lo d).toNat = (hi.toNat * 2^64 + lo.toNat) / d.toNat ∧
    (lo - div128 hi lo d * d).toNat = (hi.toNat * 2^64 + lo.toNat) % d.toNat := by
  obtain ⟨Qo, h1, h2, h3⟩ := div128Loop_spec d 64 64 hi lo 0 0 rfl (by omega) hlt (by rfl)
  simp only [Nat.zero_mul, Nat.zero_add, Nat.sub_self, Nat.pow_zero, Nat.div_one] at h3
  have hlo := lo.toNat_lt
  have hdpos : 0 < d.toNat := by omega
  have hq : Qo = (hi.toNat * 2^64 + lo.toNat) / d.toNat := by
    rw [← h3, Nat.add_comm, Nat.add_mul_div_right _ _ hdpos, Nat.div_eq_of_lt h2]; omega
  have hfit : Qo < 2^64 := by
    rw [hq, Nat.div_lt_iff_lt_mul hdpos]
    have : hi.toNat + 1 ≤ d.toNat := hlt
    omega
  have hqv : (div128 hi lo d).toNat = Qo := by
    show (div128Loop d hi lo 0 64).toNat = _
    rw [div128Loop_eq d 64 64 hi lo 0 rfl, h1, Nat.mod_eq_of_lt hfit]
  refine ⟨by rw [hqv, hq], ?_⟩
  -- remainder: lo - q*d (mod 2^64) equals the true remainder, which is < d < 2^64
  have hr : (hi.toNat * 2^64 + lo.toNat) % d.toNat = (div128LoopQR d hi lo 0 64).2.toNat := by
    rw [← h3, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]
  rw [hr]
  generalize (div128LoopQR d hi lo 0 64).2.toNat = R at h2 h3 ⊢
  rw [UInt64.toNat_sub, UInt64.toNat_mul, hqv]
  have hd := d.toNat_lt
  -- Qo*d + R = hi*2^64 + lo, so lo - Qo*d ≡ R (mod 2^64)
  have hmod : (Qo * d.toNat) % 2^64 = (Qo * d.toNat) - (Qo * d.toNat) / 2^64 * 2^64 := by
    have := Nat.div_add_mod (Qo * d.toNat) (2^64); omega
  have hkey : Qo * d.toNat + R = hi.toNat * 2^64 + lo.toNat := h3
  have hdiv : (Qo * d.toNat) / 2^64 = hi.toNat ∨ (Qo * d.toNat) / 2^64 + 1 = hi.toNat := by
    have := Nat.div_add_mod (Qo * d.toNat) (2^64)
    have := Nat.mod_lt (Qo * d.toNat) (show 0 < 2^64 by decide)
    omega
  have := Nat.div_add_mod (Qo * d.toNat) (2^64)
  have := Nat.mod_lt (Qo * d.toNat) (show 0 < 2^64 by decide)
  omega

end Lemma.Math
