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

end LeanSVM.Math
