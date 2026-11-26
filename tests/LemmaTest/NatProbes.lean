/-
  LemmaTest.NatProbes — tiny programs that exercise `Nat` lowering (LEMMA patch 0001).

  Input buffer layout (raw, not a Solana account serialization): `a : u64 @0`, `b : u64 @8`,
  `c : u64 @16`. Each probe succeeds (returns 0) iff its `Nat` expression equals `c.toNat`.
-/
import LeanSVM

open LeanSVM

namespace LemmaTest.NatProbes

@[inline] def args (input : Ptr) : SolanaM (Nat × Nat × Nat) := do
  let a ← loadU64 input 0
  let b ← loadU64 input 8
  let c ← loadU64 input 16
  return (a.toNat, b.toNat, c.toNat)

def p_add (input : Ptr) : SolanaM Unit := do
  let (a, b, c) ← args input
  SolanaM.require (a + b == c) Err.invalidArgument

def p_sub (input : Ptr) : SolanaM Unit := do
  let (a, b, c) ← args input
  SolanaM.require (a - b == c) Err.invalidArgument

def p_mul (input : Ptr) : SolanaM Unit := do
  let (a, b, c) ← args input
  SolanaM.require (a * b == c) Err.invalidArgument

def p_div (input : Ptr) : SolanaM Unit := do
  let (a, b, c) ← args input
  SolanaM.require (a / b == c) Err.invalidArgument

def p_mod (input : Ptr) : SolanaM Unit := do
  let (a, b, c) ← args input
  SolanaM.require (a % b == c) Err.invalidArgument

/-- Intermediate `a * b` may overflow even when the final result fits. -/
def p_chain (input : Ptr) : SolanaM Unit := do
  let (a, b, c) ← args input
  SolanaM.require ((a * b) / (b + 1) == c) Err.invalidArgument

/-- `ofNatTruncate` must clamp, not mask. -/
def p_trunc32 (input : Ptr) : SolanaM Unit := do
  let (a, b, c) ← args input
  SolanaM.require ((UInt32.ofNatTruncate (a + b)).toNat == c) Err.invalidArgument

def predOrZero : Nat → Nat
  | 0 => 0
  | n + 1 => n

/-- Pattern matching on `n+1`. -/
def p_pred (input : Ptr) : SolanaM Unit := do
  let (a, _, c) ← args input
  SolanaM.require (predOrZero a == c) Err.invalidArgument

def sumTo : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => sumTo n (acc + n + 1)

/-- Tail-recursive `Nat` loop (bounded by the probe: `b ≤ 64`). -/
def p_loop (input : Ptr) : SolanaM Unit := do
  let (a, b, c) ← args input
  SolanaM.require (b ≤ 64) Err.invalidArgument
  SolanaM.require (sumTo b a == c) Err.invalidArgument

/-- MUST be rejected at compile time: the literal `2^64` does not fit in a register. -/
def p_bigLiteral (input : Ptr) : SolanaM Unit := do
  let (a, _, _) ← args input
  SolanaM.require (a * a > 2 ^ 64) Err.invalidArgument

end LemmaTest.NatProbes
