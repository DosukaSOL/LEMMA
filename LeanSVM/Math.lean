/-
  LeanSVM.Math
  Overflow-safe 128-bit fixed-point arithmetic and integer square root for Solana DeFi
  (AMMs, Lending protocols, Dutch Auctions, Bonding Curves).
  Zero heap allocations, zero external dependencies, with kernel-checked Lean 4 theorems.
-/
import LeanSVM.Types
import LeanSVM.Runtime
import LeanSVM.Input
import Std.Tactic.BVDecide

namespace LeanSVM.Math

/-- Helper: 128-bit ÷ 64-bit unsigned division step loop (`rem < denom` invariant).
    Computes `⌊(hi * 2^64 + lo) / denom⌋` using 64 binary long-division steps. -/
private def div128Loop (rem lo q denom : UInt64) (steps : UInt64) : UInt64 :=
  if h : steps = 0 then
    q
  else
    let topBit := lo >>> 63
    let remCarry := rem >>> 63
    let rem1 := (rem <<< 1) ||| topBit
    let lo1 := lo <<< 1
    let q1 := q <<< 1
    if remCarry != 0 || rem1 >= denom then
      div128Loop (rem1 - denom) lo1 (q1 ||| 1) denom (steps - 1)
    else
      div128Loop rem1 lo1 q1 denom (steps - 1)
termination_by steps.toNat
decreasing_by
  all_goals
    have h1 : (1 : UInt64).toNat = 1 := rfl
    have hpos : 0 < steps.toNat := by
      have hne : steps.toNat ≠ 0 := fun hz => h (UInt64.toNat_inj.mp (by rw [hz]; rfl))
      omega
    change (steps - 1).toNat < steps.toNat
    rw [UInt64.toNat_sub_of_le, h1]
    · omega
    · exact UInt64.le_iff_toNat_le.mpr (by rw [h1]; omega)

/-- Outlined 128-bit slow path for `mulDiv64`: writes quotient to `outPtr` or fails with overflow.
    Compiled ONCE per binary (shared across all `mulDiv64` call sites!). -/
@[noinline] private def mulDiv128Slow (a b denom outPtr : UInt64) : SolanaM Unit := do
  let mask32 : UInt64 := 0xFFFFFFFF
  let aLo := a &&& mask32
  let aHi := a >>> 32
  let bLo := b &&& mask32
  let bHi := b >>> 32

  let p0 := aLo * bLo
  let p1 := aLo * bHi
  let p2 := aHi * bLo
  let p3 := aHi * bHi

  let mid := (p0 >>> 32) + (p1 &&& mask32) + (p2 &&& mask32)
  let lo := (p0 &&& mask32) ||| (mid <<< 32)
  let hi := p3 + (p1 >>> 32) + (p2 >>> 32) + (mid >>> 32)

  if hi == 0 then
    rawStoreU64 outPtr (lo / denom)
  else
    SolanaM.require (hi < denom) Err.arithmeticOverflow
    rawStoreU64 outPtr (div128Loop hi lo 0 denom 64)

/-- Exact overflow-free `⌊(a * b) / denom⌋` using full 128-bit intermediate precision!
    - Fast path (`(a ||| b) <= 0xFFFFFFFF`): single `mul64` + `div64`!
    - Full 128-bit path: calls shared `mulDiv128Slow`.
    Automatically outlined once per binary by `lean-svm` when called multiple times! -/
def mulDiv64 (a b denom : UInt64) : SolanaM UInt64 := do
  SolanaM.require (denom != 0) Err.arithmeticOverflow
  if a == 0 || b == 0 then
    return 0
  if (a ||| b) <= 0xFFFFFFFF then
    return (a * b) / denom
  else
    let outBuf ← stackAlloc 8
    mulDiv128Slow a b denom outBuf
    rawLoadU64 outBuf

/-- Ceiling division version `⌈(a * b) / denom⌉` (useful for protocol-favorable rounding). -/
def mulDiv64Ceil (a b denom : UInt64) : SolanaM UInt64 := do
  SolanaM.require (denom != 0) Err.arithmeticOverflow
  if a == 0 || b == 0 then
    return 0
  let q ← mulDiv64 a b denom
  -- Check if `(a * b) % denom != 0` via fast check when `a|b <= 0xFFFFFFFF` or conservative check
  if (a ||| b) <= 0xFFFFFFFF then
    if (a * b) % denom == 0 then return q
    else checkedAdd64 q 1
  else
    -- For large values, check `q * denom` vs `a * b` mod 2^64 (sufficient since remainder < denom)
    if q * denom == a * b then return q
    else checkedAdd64 q 1

/-- Newton-Raphson integer square root loop (converges in <= 12 iterations for any `UInt64`). -/
private def isqrtLoop (x y : UInt64) (fuel : UInt64) : UInt64 :=
  if h : fuel = 0 then
    y
  else
    let next := (y + x / y) >>> 1
    if next >= y then
      y
    else
      isqrtLoop x next (fuel - 1)
termination_by fuel.toNat
decreasing_by
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hpos : 0 < fuel.toNat := by
    have hne : fuel.toNat ≠ 0 := fun hz => h (UInt64.toNat_inj.mp (by rw [hz]; rfl))
    omega
  change (fuel - 1).toNat < fuel.toNat
  rw [UInt64.toNat_sub_of_le, h1]
  · omega
  · exact UInt64.le_iff_toNat_le.mpr (by rw [h1]; omega)

/-- Exact floor integer square root `⌊√x⌋` for any `UInt64` (0 heap, 0 stack). -/
@[noinline] def isqrt64 (x : UInt64) : UInt64 :=
  if x <= 1 then x
  else
    -- Fast initial upper-bound guess via bit-length halving
    let g0 :=
      if x >= 0x100000000 then
        if x >= 0x1000000000000 then (x >>> 24) + 1
        else (x >>> 16) + 1
      else
        if x >= 0x10000 then (x >>> 8) + 1
        else (x >>> 1) + 1
    isqrtLoop x g0 32

/-! ### Formal Verification Theorems -/

/-- Formal theorem: `mulDiv64` rejects division by zero with `Err.arithmeticOverflow`. -/
theorem mulDiv64_div_zero (a b : UInt64) (s : SvmState) :
    SolanaM.runEntry (do let _ ← mulDiv64 a b 0; pure ()) s = (Err.arithmeticOverflow, s) := by
  unfold SolanaM.runEntry mulDiv64
  simp only [Bind.bind, SolanaM.bind, SolanaM.require, SolanaM.fail, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte]

/-- Formal theorem: `mulDiv64` on 32-bit operands computes exact `(a * b) / denom` without overflow. -/
theorem mulDiv64_fast_exact (a b denom : UInt64) (s : SvmState)
    (hd : denom ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hsmall : (a ||| b) ≤ 0xFFFFFFFF) :
    mulDiv64 a b denom s = .ok ((a * b) / denom) s := by
  unfold mulDiv64
  have h1 : (denom != 0) = true := bne_iff_ne.mpr hd
  have h2 : (a == 0 || b == 0) = false := by
    simp [beq_eq_false_iff_ne, ha, hb]
  simp only [Bind.bind, Pure.pure, SolanaM.bind, SolanaM.pure, SolanaM.require,
    h1, h2, hsmall, ↓reduceIte, Bool.false_eq_true]

/-! ### Exact 128-Bit `mulDiv64` / `mulDiv64Ceil` Arithmetic & Memory-Frame Proofs -/

private theorem u64_and_mask32_toNat (x : UInt64) :
    (x &&& 0xFFFFFFFF).toNat = x.toNat % 4294967296 := by
  have h : (x &&& 0xFFFFFFFF).toNat = x.toNat % 2 ^ 32 := by
    rw [UInt64.toNat_and]
    change x.toNat &&& (2 ^ 32 - 1) = x.toNat % 2 ^ 32
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat 32
  simpa using h

private theorem u64_rsh32_toNat (x : UInt64) :
    (x >>> 32).toNat = x.toNat / 4294967296 := by
  rw [UInt64.toNat_shiftRight]
  simp [Nat.shiftRight_eq_div_pow]

private theorem u64_rsh63_toNat (x : UInt64) :
    (x >>> 63).toNat = x.toNat / 9223372036854775808 := by
  rw [UInt64.toNat_shiftRight]
  simp [Nat.shiftRight_eq_div_pow]

private theorem u64_lsh1_toNat (x : UInt64) :
    (x <<< 1).toNat = (x.toNat * 2) % 18446744073709551616 := by
  rw [UInt64.toNat_shiftLeft]
  simp [Nat.shiftLeft_eq]

private theorem u64_lsh1_or_bit_toNat (x bit : UInt64) (hb : bit.toNat ≤ 1) :
    ((x <<< 1) ||| bit).toNat = (x.toNat * 2) % 18446744073709551616 + bit.toNat := by
  have hble : bit ≤ 1 := UInt64.le_iff_toNat_le.mpr hb
  have hadd : (x <<< 1) ||| bit = (x <<< 1) + bit := by bv_decide
  rw [hadd, UInt64.toNat_add, u64_lsh1_toNat, Nat.mod_eq_of_lt]
  omega

private theorem mul_lt_2p64_of_lt_2p32 {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    x * y < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_pred_of_lt hx) (Nat.le_pred_of_lt hy)) (by decide)

private theorem u64_or_low32_high32 (x y : UInt64) :
    ((x &&& (0xFFFFFFFF : UInt64)) ||| (y <<< 32)) = (x &&& (0xFFFFFFFF : UInt64)) + (y <<< 32) := by
  bv_decide

private theorem mul128_split_exact (a b : UInt64) :
    let mask32 : UInt64 := 0xFFFFFFFF
    let aLo := a &&& mask32
    let aHi := a >>> 32
    let bLo := b &&& mask32
    let bHi := b >>> 32
    let p0 := aLo * bLo
    let p1 := aLo * bHi
    let p2 := aHi * bLo
    let p3 := aHi * bHi
    let mid := (p0 >>> 32) + (p1 &&& mask32) + (p2 &&& mask32)
    let lo := (p0 &&& mask32) ||| (mid <<< 32)
    let hi := p3 + (p1 >>> 32) + (p2 >>> 32) + (mid >>> 32)
    hi.toNat * 18446744073709551616 + lo.toNat = a.toNat * b.toNat := by
  dsimp only
  let mask32 : UInt64 := 0xFFFFFFFF
  have haLo : (a &&& mask32).toNat = a.toNat % 2 ^ 32 := u64_and_mask32_toNat a
  have haHi : (a >>> 32).toNat = a.toNat / 2 ^ 32 := u64_rsh32_toNat a
  have hbLo : (b &&& mask32).toNat = b.toNat % 2 ^ 32 := u64_and_mask32_toNat b
  have hbHi : (b >>> 32).toNat = b.toNat / 2 ^ 32 := u64_rsh32_toNat b
  have haLt : a.toNat < 2 ^ 64 := a.toNat_lt
  have hbLt : b.toNat < 2 ^ 64 := b.toNat_lt
  have haHiLt : a.toNat / 2 ^ 32 < 2 ^ 32 := by omega
  have hbHiLt : b.toNat / 2 ^ 32 < 2 ^ 32 := by omega
  have haLoLt : a.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hbLoLt : b.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  let P0 : UInt64 := (a &&& mask32) * (b &&& mask32)
  let P1 : UInt64 := (a &&& mask32) * (b >>> 32)
  let P2 : UInt64 := (a >>> 32) * (b &&& mask32)
  let P3 : UInt64 := (a >>> 32) * (b >>> 32)
  have hp0 : P0.toNat = (a.toNat % 2 ^ 32) * (b.toNat % 2 ^ 32) := by
    show ((a &&& mask32) * (b &&& mask32)).toNat = _
    rw [UInt64.toNat_mul, haLo, hbLo, Nat.mod_eq_of_lt (mul_lt_2p64_of_lt_2p32 haLoLt hbLoLt)]
  have hp1 : P1.toNat = (a.toNat % 2 ^ 32) * (b.toNat / 2 ^ 32) := by
    show ((a &&& mask32) * (b >>> 32)).toNat = _
    rw [UInt64.toNat_mul, haLo, hbHi, Nat.mod_eq_of_lt (mul_lt_2p64_of_lt_2p32 haLoLt hbHiLt)]
  have hp2 : P2.toNat = (a.toNat / 2 ^ 32) * (b.toNat % 2 ^ 32) := by
    show ((a >>> 32) * (b &&& mask32)).toNat = _
    rw [UInt64.toNat_mul, haHi, hbLo, Nat.mod_eq_of_lt (mul_lt_2p64_of_lt_2p32 haHiLt hbLoLt)]
  have hp3 : P3.toNat = (a.toNat / 2 ^ 32) * (b.toNat / 2 ^ 32) := by
    show ((a >>> 32) * (b >>> 32)).toNat = _
    rw [UInt64.toNat_mul, haHi, hbHi, Nat.mod_eq_of_lt (mul_lt_2p64_of_lt_2p32 haHiLt hbHiLt)]
  have hP0lt : P0.toNat < 2 ^ 64 := P0.toNat_lt
  have hP1lt : P1.toNat < 2 ^ 64 := P1.toNat_lt
  have hP2lt : P2.toNat < 2 ^ 64 := P2.toNat_lt
  let MID : UInt64 := (P0 >>> 32) + (P1 &&& mask32) + (P2 &&& mask32)
  have hmid : MID.toNat = P0.toNat / 2 ^ 32 + P1.toNat % 2 ^ 32 + P2.toNat % 2 ^ 32 := by
    show ((P0 >>> 32) + (P1 &&& mask32) + (P2 &&& mask32)).toNat = _
    rw [UInt64.toNat_add, UInt64.toNat_add, u64_rsh32_toNat, u64_and_mask32_toNat, u64_and_mask32_toNat]
    have h1 : P0.toNat / 2 ^ 32 + P1.toNat % 2 ^ 32 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt]; omega
  have hlo : ((P0 &&& mask32) ||| (MID <<< 32)).toNat =
      P0.toNat % 2 ^ 32 + (MID.toNat % 2 ^ 32) * 2 ^ 32 := by
    have hshift : (MID <<< 32).toNat = (MID.toNat % 2 ^ 32) * 2 ^ 32 := by
      rw [UInt64.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]
      conv => lhs; rw [show (18446744073709551616 : Nat) = 4294967296 * 4294967296 by decide]
      rw [Nat.mul_comm MID.toNat, Nat.mul_mod_mul_left, Nat.mul_comm]
    rw [u64_or_low32_high32 P0 MID, UInt64.toNat_add, u64_and_mask32_toNat, hshift, Nat.mod_eq_of_lt]
    have h1 : P0.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    have h2 : MID.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    omega
  have hhi : (P3 + (P1 >>> 32) + (P2 >>> 32) + (MID >>> 32)).toNat =
      P3.toNat + P1.toNat / 2 ^ 32 + P2.toNat / 2 ^ 32 + MID.toNat / 2 ^ 32 := by
    have hP3b : P3.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := by
      rw [hp3]; exact Nat.mul_le_mul (Nat.le_pred_of_lt haHiLt) (Nat.le_pred_of_lt hbHiLt)
    have hP1m : P1.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := by
      rw [hp1]; exact Nat.mul_le_mul (Nat.le_pred_of_lt haLoLt) (Nat.le_pred_of_lt hbHiLt)
    have hP2m : P2.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := by
      rw [hp2]; exact Nat.mul_le_mul (Nat.le_pred_of_lt haHiLt) (Nat.le_pred_of_lt hbLoLt)
    have hP1b : P1.toNat / 2 ^ 32 ≤ 2 ^ 32 - 2 := by omega
    have hP2b : P2.toNat / 2 ^ 32 ≤ 2 ^ 32 - 2 := by omega
    have hMIDb : MID.toNat / 2 ^ 32 ≤ 2 := by rw [hmid]; omega
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add,
        u64_rsh32_toNat, u64_rsh32_toNat, u64_rsh32_toNat]
    have s1 : P3.toNat + P1.toNat / 2 ^ 32 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt s1]
    have s2 : P3.toNat + P1.toNat / 2 ^ 32 + P2.toNat / 2 ^ 32 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt s2, Nat.mod_eq_of_lt]; omega
  change (P3 + (P1 >>> 32) + (P2 >>> 32) + (MID >>> 32)).toNat * 18446744073709551616 +
      ((P0 &&& mask32) ||| (MID <<< 32)).toNat = a.toNat * b.toNat
  rw [hhi, hlo]
  have hab : a.toNat * b.toNat =
      P3.toNat * 18446744073709551616 + (P1.toNat + P2.toNat) * 4294967296 + P0.toNat := by
    have haD : a.toNat = (a.toNat / 2 ^ 32) * 2 ^ 32 + a.toNat % 2 ^ 32 :=
      (Nat.div_add_mod' a.toNat (2 ^ 32)).symm
    have hbD : b.toNat = (b.toNat / 2 ^ 32) * 2 ^ 32 + b.toNat % 2 ^ 32 :=
      (Nat.div_add_mod' b.toNat (2 ^ 32)).symm
    rw [hp0, hp1, hp2, hp3]
    conv => lhs; rw [haD, hbD]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
    have h1 : 2 ^ 32 * (b.toNat / 2 ^ 32 * 2 ^ 32) = (b.toNat / 2 ^ 32) * 18446744073709551616 := by
      rw [Nat.mul_comm (2 ^ 32), Nat.mul_assoc]
    have h2 : 2 ^ 32 * (b.toNat % 2 ^ 32) = (b.toNat % 2 ^ 32) * 2 ^ 32 := Nat.mul_comm _ _
    rw [h1, h2]
    simp only [← Nat.mul_assoc]
    omega
  rw [hab]
  have hP0d : P0.toNat = (P0.toNat / 4294967296) * 4294967296 + P0.toNat % 4294967296 :=
    (Nat.div_add_mod' P0.toNat 4294967296).symm
  have hP1d : P1.toNat = (P1.toNat / 4294967296) * 4294967296 + P1.toNat % 4294967296 :=
    (Nat.div_add_mod' P1.toNat 4294967296).symm
  have hP2d : P2.toNat = (P2.toNat / 4294967296) * 4294967296 + P2.toNat % 4294967296 :=
    (Nat.div_add_mod' P2.toNat 4294967296).symm
  have hMIDd : MID.toNat = (MID.toNat / 4294967296) * 4294967296 + MID.toNat % 4294967296 :=
    (Nat.div_add_mod' MID.toNat 4294967296).symm
  have hmid' : MID.toNat = P0.toNat / 4294967296 + P1.toNat % 4294967296 + P2.toNat % 4294967296 := hmid
  omega

private theorem div128Loop_exact :
    ∀ (n : Nat) (rem lo q denom steps : UInt64),
      steps.toNat = n →
      n ≤ 64 →
      0 < denom.toNat →
      rem.toNat < denom.toNat →
      q.toNat * 2 ^ n + (rem.toNat * 2 ^ n + lo.toNat / 2 ^ (64 - n)) / denom.toNat < 2 ^ 64 →
      (div128Loop rem lo q denom steps).toNat =
        q.toNat * 2 ^ n + (rem.toNat * 2 ^ n + lo.toNat / 2 ^ (64 - n)) / denom.toNat := by
  intro n
  induction n with
  | zero =>
    intro rem lo q denom steps hn _ hd hrem _
    have h0 : steps = 0 := UInt64.toNat_inj.mp hn
    rw [div128Loop]; simp only [h0, ↓reduceDIte]
    have hlo0 : lo.toNat / 2 ^ 64 = 0 := Nat.div_eq_of_lt lo.toNat_lt
    have hrem0 : rem.toNat / denom.toNat = 0 := Nat.div_eq_of_lt hrem
    simp [hlo0, hrem0]
  | succ m ih =>
    intro rem lo q denom steps hn hle hd hrem hbound
    have hne : steps ≠ 0 := by intro h; rw [h] at hn; simp at hn
    rw [div128Loop]; simp only [hne, ↓reduceDIte]
    have hsub : (steps - 1).toNat = m := by
      have h1 : (1 : UInt64).toNat = 1 := rfl
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [h1, hn]; omega)), hn, h1]
      omega
    have htb : (lo >>> 63).toNat = lo.toNat / 2 ^ 63 := u64_rsh63_toNat lo
    have htbLe : (lo >>> 63).toNat ≤ 1 := by rw [htb]; have := lo.toNat_lt; omega
    have hlo1 : (lo <<< 1).toNat = (lo.toNat * 2) % 2 ^ 64 := u64_lsh1_toNat lo
    have hloSplit : lo.toNat / 2 ^ (64 - (m + 1)) =
        (lo >>> 63).toNat * 2 ^ m + (lo <<< 1).toNat / 2 ^ (64 - m) := by
      rw [htb, hlo1]
      have hpow : 64 - m = (63 - m) + 1 := by omega
      have hpow2 : 2 ^ 63 = 2 ^ m * 2 ^ (63 - m) := by rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
      have hlo_mod : (lo.toNat * 2) % 2 ^ 64 = 2 * (lo.toNat % 2 ^ 63) := by
        have h64 : (2 ^ 64 : Nat) = 2 * 2 ^ 63 := by decide
        rw [h64, Nat.mul_comm lo.toNat 2, Nat.mul_mod_mul_left]
      have h2eq : 2 ^ (63 - m + 1) = 2 * 2 ^ (63 - m) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hlo_mod, hpow, h2eq, Nat.mul_div_mul_left _ _ (by decide)]
      have hdiv : lo.toNat = (lo.toNat / 2 ^ 63) * 2 ^ 63 + lo.toNat % 2 ^ 63 :=
        (Nat.div_add_mod' lo.toNat (2 ^ 63)).symm
      have hsub1 : 64 - (m + 1) = 63 - m := by omega
      rw [hsub1]
      conv => lhs; rw [hdiv, hpow2, ← Nat.mul_assoc, Nat.add_comm]
      rw [Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide : 0 < 2)), Nat.add_comm, ← hpow2]
    have hrem1 : ((rem <<< 1) ||| (lo >>> 63)).toNat =
        (rem.toNat * 2) % 2 ^ 64 + (lo >>> 63).toNat := u64_lsh1_or_bit_toNat rem (lo >>> 63) htbLe
    have hrc : (rem >>> 63).toNat = rem.toNat / 2 ^ 63 := u64_rsh63_toNat rem
    have hremFullEq : rem.toNat * 2 ^ (m + 1) + lo.toNat / 2 ^ (64 - (m + 1)) =
        (2 * rem.toNat + (lo >>> 63).toNat) * 2 ^ m + (lo <<< 1).toNat / 2 ^ (64 - m) := by
      rw [hloSplit, Nat.pow_succ, Nat.add_mul]
      have h1 : rem.toNat * (2 ^ m * 2) = (2 * rem.toNat) * 2 ^ m := by
        rw [Nat.mul_comm (2 ^ m) 2, ← Nat.mul_assoc, Nat.mul_comm rem.toNat 2]
      rw [h1, Nat.add_assoc]
    have hqBound : q.toNat * 2 < 2 ^ 64 := by
      have hpm : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
      have h1 : q.toNat * 2 ^ (m + 1) < 2 ^ 64 :=
        Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hbound
      have h2 : q.toNat * 2 ≤ q.toNat * (2 * 2 ^ m) := by
        rw [← Nat.mul_assoc]; exact Nat.le_mul_of_pos_right _ (by omega)
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ m) 2] at h1
      exact Nat.lt_of_le_of_lt h2 h1
    have hq1 : (q <<< 1).toNat = q.toNat * 2 := by
      rw [u64_lsh1_toNat, Nat.mod_eq_of_lt hqBound]
    have hq1Or : ((q <<< 1) ||| 1).toNat = q.toNat * 2 + 1 := by
      have h := u64_lsh1_or_bit_toNat q 1 (by decide)
      rw [Nat.mod_eq_of_lt hqBound] at h; exact h
    let rem1 : UInt64 := (rem <<< 1) ||| (lo >>> 63)
    let remFull : Nat := 2 * rem.toNat + (lo >>> 63).toNat
    by_cases hcond : ((rem >>> 63) != 0 || ((rem <<< 1) ||| (lo >>> 63)) >= denom) = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hcond)]
      have hge : denom.toNat ≤ remFull := by
        simp only [Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq] at hcond
        rcases hcond with hc | hg
        · have hne0 : (rem >>> 63).toNat ≠ 0 := fun h => hc (UInt64.toNat_inj.mp h)
          rw [hrc] at hne0
          have : denom.toNat < 2 ^ 64 := denom.toNat_lt
          omega
        · have hgle : denom.toNat ≤ rem1.toNat := UInt64.le_iff_toNat_le.mp hg
          change denom.toNat ≤ ((rem <<< 1) ||| (lo >>> 63)).toNat at hgle
          rw [hrem1] at hgle
          have : (rem.toNat * 2) % 2 ^ 64 ≤ rem.toNat * 2 := Nat.mod_le _ _
          omega
      have hsubRem : (rem1 - denom).toNat = remFull - denom.toNat := by
        by_cases hhi : rem.toNat < 2 ^ 63
        · have hrem1_eq : rem1.toNat = remFull := by
            show ((rem <<< 1) ||| (lo >>> 63)).toNat = 2 * rem.toNat + (lo >>> 63).toNat
            rw [hrem1, Nat.mod_eq_of_lt (by omega)]; omega
          rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), hrem1_eq]
        · have hrem1_eq : rem1.toNat = remFull - 2 ^ 64 := by
            have : rem.toNat < 2 ^ 64 := rem.toNat_lt
            have hmod : (rem.toNat * 2) % 2 ^ 64 = rem.toNat * 2 - 2 ^ 64 := by omega
            show ((rem <<< 1) ||| (lo >>> 63)).toNat = _
            rw [hrem1, hmod]; omega
          have hlt : rem1.toNat < denom.toNat := by
            have : rem.toNat < denom.toNat := hrem
            have : denom.toNat < 2 ^ 64 := denom.toNat_lt
            omega
          have hwrap : (rem1 - denom).toNat = 2 ^ 64 + rem1.toNat - denom.toNat := by
            rw [UInt64.toNat_sub]
            have hsz : UInt64.size = 2 ^ 64 := rfl
            have : denom.toNat < 2 ^ 64 := denom.toNat_lt
            omega
          rw [hwrap, hrem1_eq]
          have : rem.toNat < 2 ^ 64 := rem.toNat_lt
          omega
      have hsubLt : (rem1 - denom).toNat < denom.toNat := by omega
      have hstepEq :
          ((q <<< 1) ||| 1).toNat * 2 ^ m +
            ((rem1 - denom).toNat * 2 ^ m + (lo <<< 1).toNat / 2 ^ (64 - m)) / denom.toNat =
          q.toNat * 2 ^ (m + 1) + (rem.toNat * 2 ^ (m + 1) + lo.toNat / 2 ^ (64 - (m + 1))) / denom.toNat := by
        rw [hq1Or, hsubRem, hremFullEq]
        have hadd : remFull * 2 ^ m + (lo <<< 1).toNat / 2 ^ (64 - m) =
            ((remFull - denom.toNat) * 2 ^ m + (lo <<< 1).toNat / 2 ^ (64 - m)) + 2 ^ m * denom.toNat := by
          have hmul : (remFull - denom.toNat) * 2 ^ m + denom.toNat * 2 ^ m = remFull * 2 ^ m := by
            rw [← Nat.add_mul, Nat.sub_add_cancel hge]
          have hcomm : 2 ^ m * denom.toNat = denom.toNat * 2 ^ m := Nat.mul_comm _ _
          omega
        rw [hadd, Nat.add_mul_div_right _ _ hd, Nat.pow_succ, Nat.add_mul, Nat.one_mul]
        have hq2 : (q.toNat * 2) * 2 ^ m = q.toNat * (2 ^ m * 2) := by
          rw [Nat.mul_assoc, Nat.mul_comm 2 (2 ^ m)]
        omega
      rw [ih (rem1 - denom) (lo <<< 1) ((q <<< 1) ||| 1) denom (steps - 1) hsub (by omega) hd hsubLt (by rw [hstepEq]; exact hbound)]
      exact hstepEq
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hcond)]
      have hnot : (rem >>> 63) = 0 ∧ rem1.toNat < denom.toNat := by
        simp only [Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq, not_or] at hcond
        exact ⟨Decidable.not_not.mp hcond.1, Nat.lt_of_not_ge (fun hle' => hcond.2 (UInt64.le_iff_toNat_le.mpr hle'))⟩
      have hhi : rem.toNat < 2 ^ 63 := by
        have h0 : (rem >>> 63).toNat = 0 := congrArg UInt64.toNat hnot.1
        rw [hrc] at h0; omega
      have hrem1_eq : rem1.toNat = remFull := by
        show ((rem <<< 1) ||| (lo >>> 63)).toNat = 2 * rem.toNat + (lo >>> 63).toNat
        rw [hrem1, Nat.mod_eq_of_lt (by omega)]; omega
      have hstepEq :
          (q <<< 1).toNat * 2 ^ m +
            (rem1.toNat * 2 ^ m + (lo <<< 1).toNat / 2 ^ (64 - m)) / denom.toNat =
          q.toNat * 2 ^ (m + 1) + (rem.toNat * 2 ^ (m + 1) + lo.toNat / 2 ^ (64 - (m + 1))) / denom.toNat := by
        rw [hq1, hrem1_eq, hremFullEq, Nat.pow_succ]
        have hq2 : (q.toNat * 2) * 2 ^ m = q.toNat * (2 ^ m * 2) := by
          rw [Nat.mul_assoc, Nat.mul_comm 2 (2 ^ m)]
        rw [hq2]
      rw [ih rem1 (lo <<< 1) (q <<< 1) denom (steps - 1) hsub (by omega) hd hnot.2 (by rw [hstepEq]; exact hbound)]
      exact hstepEq

/-- **THEOREM (`LeanSVM.Math.mulDiv64` Exact 128-Bit Floor Division & Memory Frame)**:
    Whenever `mulDiv64 a b denom s = .ok q s'` (on EITHER the 64-bit fast path OR the full
    128-bit `mulDiv128Slow` path):
    1. `denom.toNat > 0` and `q.toNat = (a.toNat * b.toNat) / denom.toNat` EXACTLY!
    2. Every memory byte outside the 8-byte stack scratch `[s.stackSp - 8, s.stackSp)` is
       bit-for-bit preserved (`s'.mem x = s.mem x`)! -/
theorem mulDiv64_ok_spec (a b denom q : UInt64) (s s' : SvmState)
    (hsp : 8 ≤ s.stackSp.toNat)
    (h : mulDiv64 a b denom s = .ok q s') :
    0 < denom.toNat ∧
    q.toNat = (a.toNat * b.toNat) / denom.toNat ∧
    (s'.stackSp = s.stackSp ∨ s'.stackSp = s.stackSp - 8) ∧
    (∀ x : UInt64, (x < s.stackSp - 8 ∨ s.stackSp ≤ x) → s'.mem x = s.mem x) := by
  unfold mulDiv64 at h
  simp only [Bind.bind, Pure.pure, SolanaM.bind, SolanaM.require] at h
  by_cases hd : (denom != 0) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hd)] at h
    dsimp only [SolanaM.pure] at h
    have hdPos : 0 < denom.toNat := by
      have hne : denom ≠ 0 := bne_iff_ne.mp hd
      have hne0 : denom.toNat ≠ 0 := fun hz => hne (UInt64.toNat_inj.mp hz)
      omega
    by_cases hz : (a == 0 || b == 0) = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hz)] at h
      cases h
      simp only [Bool.or_eq_true, beq_iff_eq] at hz
      refine ⟨hdPos, ?_, Or.inl rfl, fun _ _ => rfl⟩
      rcases hz with rfl | rfl <;> simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hz)] at h
      by_cases hsm : (a ||| b) ≤ 0xFFFFFFFF
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hsm)] at h
        cases h
        have haLe : a ≤ 0xFFFFFFFF := by bv_decide
        have hbLe : b ≤ 0xFFFFFFFF := by bv_decide
        have ha32 : a.toNat < 2 ^ 32 := by
          have := UInt64.le_iff_toNat_le.mp haLe
          have : (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 := by decide
          omega
        have hb32 : b.toNat < 2 ^ 32 := by
          have := UInt64.le_iff_toNat_le.mp hbLe
          have : (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 := by decide
          omega
        have hmul : (a * b).toNat = a.toNat * b.toNat := by
          rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (mul_lt_2p64_of_lt_2p32 ha32 hb32)]
        refine ⟨hdPos, ?_, Or.inl rfl, fun _ _ => rfl⟩
        rw [UInt64.toNat_div, hmul]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hsm)] at h
        unfold stackAlloc rawStackAlloc mulDiv128Slow rawStoreU64 rawLoadU64 at h
        simp only [Bind.bind, SolanaM.require] at h
        dsimp only [SolanaM.bind, SolanaM.pure] at h
        have halign : ((8 + 7 : UInt64) &&& 0xFFFFFFFFFFFFFFF8) = 8 := by decide
        rw [halign] at h
        have hsplit := mul128_split_exact a b
        dsimp only at hsplit
        let mask32 : UInt64 := 0xFFFFFFFF
        let hi : UInt64 := (a >>> 32) * (b >>> 32) +
          (((a &&& mask32) * (b >>> 32)) >>> 32) +
          (((a >>> 32) * (b &&& mask32)) >>> 32) +
          ((((((a &&& mask32) * (b &&& mask32)) >>> 32) +
            (((a &&& mask32) * (b >>> 32)) &&& mask32) +
            (((a >>> 32) * (b &&& mask32)) &&& mask32))) >>> 32)
        let lo : UInt64 := (((a &&& mask32) * (b &&& mask32)) &&& mask32) |||
          (((((a &&& mask32) * (b &&& mask32)) >>> 32) +
            (((a &&& mask32) * (b >>> 32)) &&& mask32) +
            (((a >>> 32) * (b &&& mask32)) &&& mask32)) <<< 32)
        have hsp_sub : (s.stackSp - 8).toNat = s.stackSp.toNat - 8 := by
          rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (show (8 : UInt64).toNat ≤ s.stackSp.toNat from hsp))]; rfl
        have hsp_le : s.stackSp - 8 ≤ 0xFFFFFFFFFFFFFFF7 := by
          apply UInt64.le_iff_toNat_le.mpr
          rw [hsp_sub]
          have : s.stackSp.toNat < 2 ^ 64 := s.stackSp.toNat_lt
          have : (0xFFFFFFFFFFFFFFF7 : UInt64).toNat = 2 ^ 64 - 9 := by decide
          omega
        have hsp_add : (s.stackSp - 8) + 8 = s.stackSp := by bv_decide
        by_cases hhi0 : (hi == 0) = true
        · have hhi0' := hhi0
          dsimp only [hi, mask32] at hhi0'
          rw [ite_eq_left_of_eq_true _ _ (eq_true hhi0')] at h
          cases h
          have hhiZero : hi.toNat = 0 := congrArg UInt64.toNat (beq_iff_eq.mp hhi0)
          change hi.toNat * 18446744073709551616 + lo.toNat = a.toNat * b.toNat at hsplit
          rw [hhiZero] at hsplit; simp only [Nat.zero_mul, Nat.zero_add] at hsplit
          refine ⟨hdPos, ?_, Or.inr rfl, ?_⟩
          · rw [SvmState.readU64_writeU64_same, UInt64.toNat_div]
            exact congrArg (· / denom.toNat) hsplit
          · intro x hx
            have hx' : x < s.stackSp - 8 ∨ (s.stackSp - 8) + 8 ≤ x := by rwa [hsp_add]
            exact SvmState.mem_writeU64_outside { s with stackSp := s.stackSp - 8 } (s.stackSp - 8) x _ hsp_le hx'
        · have hhi0' := hhi0
          dsimp only [hi, mask32] at hhi0'
          rw [ite_eq_right_of_eq_false _ _ (eq_false hhi0')] at h
          simp only [decide_eq_true_eq] at h
          by_cases hlt : hi < denom
          · have hlt' := hlt
            dsimp only [hi, mask32] at hlt'
            rw [ite_eq_left_of_eq_true _ _ (eq_true hlt')] at h
            unfold SolanaM.bind at h
            dsimp only [SolanaM.pure] at h
            cases h
            have hhiLt : hi.toNat < denom.toNat := UInt64.lt_iff_toNat_lt.mp hlt
            have hqLt : (hi.toNat * 2 ^ 64 + lo.toNat) / denom.toNat < 2 ^ 64 := by
              apply Nat.div_lt_of_lt_mul
              have hloLt : lo.toNat < 2 ^ 64 := lo.toNat_lt
              have hleD : hi.toNat + 1 ≤ denom.toNat := hhiLt
              have hmul : (hi.toNat + 1) * 2 ^ 64 ≤ denom.toNat * 2 ^ 64 :=
                Nat.mul_le_mul_right (2 ^ 64) hleD
              rw [Nat.add_mul, Nat.one_mul] at hmul
              rw [Nat.mul_comm denom.toNat (2 ^ 64)] at hmul
              omega
            have hdiv := div128Loop_exact 64 hi lo 0 denom 64 rfl (by omega) hdPos hhiLt (by simpa using hqLt)
            refine ⟨hdPos, ?_, Or.inr rfl, ?_⟩
            · rw [SvmState.readU64_writeU64_same]
              change (div128Loop hi lo 0 denom 64).toNat = _
              rw [hdiv]
              change 0 * 2 ^ 64 + (hi.toNat * 2 ^ 64 + lo.toNat / 2 ^ (64 - 64)) / denom.toNat = _
              simp only [Nat.zero_mul, Nat.zero_add, Nat.sub_self, Nat.pow_zero, Nat.div_one]
              exact congrArg (· / denom.toNat) hsplit
            · intro x hx
              have hx' : x < s.stackSp - 8 ∨ (s.stackSp - 8) + 8 ≤ x := by rwa [hsp_add]
              exact SvmState.mem_writeU64_outside { s with stackSp := s.stackSp - 8 } (s.stackSp - 8) x _ hsp_le hx'
          · have hlt' := hlt
            dsimp only [hi, mask32] at hlt'
            rw [ite_eq_right_of_eq_false _ _ (eq_false hlt')] at h
            unfold SolanaM.bind at h
            dsimp only [SolanaM.fail] at h; cases h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hd)] at h; dsimp only [SolanaM.fail] at h; cases h

/-- **THEOREM (`LeanSVM.Math.mulDiv64Ceil` Exact 128-Bit Ceiling Division & Memory Frame)**:
    Whenever `mulDiv64Ceil a b denom s = .ok q s'`:
    1. `denom.toNat > 0` and `q.toNat = (a.toNat * b.toNat + denom.toNat - 1) / denom.toNat` (exact ceiling!)
    2. `s'.stackSp = s.stackSp ∨ s'.stackSp = s.stackSp - 8`.
    3. Every memory byte outside `[s.stackSp - 8, s.stackSp)` is bit-for-bit preserved! -/
theorem mulDiv64Ceil_ok_spec (a b denom q : UInt64) (s s' : SvmState)
    (hsp : 8 ≤ s.stackSp.toNat)
    (h : mulDiv64Ceil a b denom s = .ok q s') :
    0 < denom.toNat ∧
    q.toNat = (a.toNat * b.toNat + denom.toNat - 1) / denom.toNat ∧
    (s'.stackSp = s.stackSp ∨ s'.stackSp = s.stackSp - 8) ∧
    (∀ x : UInt64, (x < s.stackSp - 8 ∨ s.stackSp ≤ x) → s'.mem x = s.mem x) := by
  unfold mulDiv64Ceil at h
  simp only [Bind.bind, Pure.pure, SolanaM.bind, SolanaM.require] at h
  by_cases hd : (denom != 0) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hd)] at h
    dsimp only [SolanaM.pure] at h
    have hdPos : 0 < denom.toNat := by
      have hne : denom ≠ 0 := bne_iff_ne.mp hd
      have hne0 : denom.toNat ≠ 0 := fun hz => hne (UInt64.toNat_inj.mp hz)
      omega
    by_cases hz : (a == 0 || b == 0) = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hz)] at h
      cases h
      simp only [Bool.or_eq_true, beq_iff_eq] at hz
      refine ⟨hdPos, ?_, Or.inl rfl, fun _ _ => rfl⟩
      rcases hz with rfl | rfl <;> simp [Nat.div_eq_of_lt (by omega : denom.toNat - 1 < denom.toNat)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hz)] at h
      unfold SolanaM.bind at h
      cases hmd : mulDiv64 a b denom s with
      | err c st => rw [hmd] at h; cases h
      | ok q0 s1 =>
        rw [hmd] at h
        dsimp only at h
        have ⟨_, hq0, hsp1, hmem1⟩ := mulDiv64_ok_spec a b denom q0 s s1 hsp hmd
        have hrem_eq : a.toNat * b.toNat = q0.toNat * denom.toNat + (a.toNat * b.toNat) % denom.toNat := by
          rw [hq0]; exact (Nat.div_add_mod' _ _).symm
        have hremLt : (a.toNat * b.toNat) % denom.toNat < denom.toNat := Nat.mod_lt _ hdPos
        have hceil_zero : (a.toNat * b.toNat) % denom.toNat = 0 →
            (a.toNat * b.toNat + denom.toNat - 1) / denom.toNat = q0.toNat := by
          intro hr0
          have h1 : a.toNat * b.toNat + denom.toNat - 1 = denom.toNat * q0.toNat + (denom.toNat - 1) := by
            rw [Nat.mul_comm denom.toNat q0.toNat]; omega
          rw [h1, Nat.mul_add_div hdPos, Nat.div_eq_of_lt (by omega : denom.toNat - 1 < denom.toNat)]; omega
        have hceil_pos : (a.toNat * b.toNat) % denom.toNat ≠ 0 →
            (a.toNat * b.toNat + denom.toNat - 1) / denom.toNat = q0.toNat + 1 := by
          intro hrp
          have h1 : a.toNat * b.toNat + denom.toNat - 1 =
              denom.toNat * (q0.toNat + 1) + ((a.toNat * b.toNat) % denom.toNat - 1) := by
            rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm denom.toNat q0.toNat]; omega
          rw [h1, Nat.mul_add_div hdPos, Nat.div_eq_of_lt (by omega : (a.toNat * b.toNat) % denom.toNat - 1 < denom.toNat)]
        have hchk : ∀ q' : UInt64, checkedAdd64 q0 1 s1 = .ok q' s' → q'.toNat = q0.toNat + 1 ∧ s' = s1 := by
          intro q' hc
          unfold checkedAdd64 at hc
          simp only [Bind.bind, Pure.pure, SolanaM.bind, SolanaM.require, decide_eq_true_eq] at hc
          by_cases hov : q0 + 1 ≥ q0
          · rw [ite_eq_left_of_eq_true _ _ (eq_true hov)] at hc
            dsimp only [SolanaM.pure] at hc
            cases hc
            have hle : q0.toNat ≤ (q0 + 1).toNat := UInt64.le_iff_toNat_le.mp hov
            have h1 : (1 : UInt64).toNat = 1 := rfl
            have hlt : q0.toNat + 1 < 2 ^ 64 := by
              rcases Nat.lt_or_ge (q0.toNat + 1) (2 ^ 64) with hlt | hge
              · exact hlt
              · exfalso
                have : (q0 + 1).toNat = 0 := by
                  rw [UInt64.toNat_add, h1]
                  have := q0.toNat_lt; omega
                have := q0.toNat_lt; omega
            exact ⟨by rw [UInt64.toNat_add, h1, Nat.mod_eq_of_lt hlt], rfl⟩
          · rw [ite_eq_right_of_eq_false _ _ (eq_false hov)] at hc; dsimp only [SolanaM.fail] at hc; cases hc
        by_cases hsm : (a ||| b) ≤ 0xFFFFFFFF
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hsm)] at h
          have haLe : a ≤ 0xFFFFFFFF := by bv_decide
          have hbLe : b ≤ 0xFFFFFFFF := by bv_decide
          have ha32 : a.toNat < 2 ^ 32 := by
            have := UInt64.le_iff_toNat_le.mp haLe
            have : (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 := by decide
            omega
          have hb32 : b.toNat < 2 ^ 32 := by
            have := UInt64.le_iff_toNat_le.mp hbLe
            have : (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 := by decide
            omega
          have hmul : (a * b).toNat = a.toNat * b.toNat := by
            rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (mul_lt_2p64_of_lt_2p32 ha32 hb32)]
          by_cases hmod0 : ((a * b) % denom == 0) = true
          · rw [ite_eq_left_of_eq_true _ _ (eq_true hmod0)] at h; cases h
            have hr0 : (a.toNat * b.toNat) % denom.toNat = 0 := by
              have := congrArg UInt64.toNat (beq_iff_eq.mp hmod0)
              rwa [UInt64.toNat_mod, hmul] at this
            exact ⟨hdPos, (hceil_zero hr0).symm, hsp1, hmem1⟩
          · rw [ite_eq_right_of_eq_false _ _ (eq_false hmod0)] at h
            have ⟨hq', hs'⟩ := hchk q h
            have hrp : (a.toNat * b.toNat) % denom.toNat ≠ 0 := by
              intro hr0
              apply hmod0; apply beq_iff_eq.mpr; apply UInt64.toNat_inj.mp
              rw [UInt64.toNat_mod, hmul]; exact hr0
            exact ⟨hdPos, by rw [hq', hceil_pos hrp], by rw [hs']; exact hsp1, fun x hx => by rw [hs']; exact hmem1 x hx⟩
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hsm)] at h
          have hmod_iff : (q0 * denom == a * b) = true ↔ (a.toNat * b.toNat) % denom.toNat = 0 := by
            rw [beq_iff_eq]
            constructor
            · intro heq
              have htn := congrArg UInt64.toNat heq
              rw [UInt64.toNat_mul, UInt64.toNat_mul] at htn
              have hrLt64 : (a.toNat * b.toNat) % denom.toNat < 2 ^ 64 := Nat.lt_trans hremLt denom.toNat_lt
              have hcongr : (q0.toNat * denom.toNat + (a.toNat * b.toNat) % denom.toNat) % 2 ^ 64 =
                  (q0.toNat * denom.toNat) % 2 ^ 64 := by rw [← hrem_eq, ← htn]
              omega
            · intro hr0
              apply UInt64.toNat_inj.mp
              rw [UInt64.toNat_mul, UInt64.toNat_mul, hrem_eq, hr0, Nat.add_zero]
          by_cases hqd : (q0 * denom == a * b) = true
          · rw [ite_eq_left_of_eq_true _ _ (eq_true hqd)] at h; cases h
            exact ⟨hdPos, (hceil_zero (hmod_iff.mp hqd)).symm, hsp1, hmem1⟩
          · rw [ite_eq_right_of_eq_false _ _ (eq_false hqd)] at h
            have ⟨hq', hs'⟩ := hchk q h
            have hrp : (a.toNat * b.toNat) % denom.toNat ≠ 0 := fun hr0 => hqd (hmod_iff.mpr hr0)
            exact ⟨hdPos, by rw [hq', hceil_pos hrp], by rw [hs']; exact hsp1, fun x hx => by rw [hs']; exact hmem1 x hx⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hd)] at h; dsimp only [SolanaM.fail] at h; cases h

end LeanSVM.Math
