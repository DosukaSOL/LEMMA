/-
  LemmaTest.ChainProbes — probe programs for the REAL SVM (LiteSVM in CI). Arguments are read from
  instruction data (the real loader always passes an ABI-serialized buffer). Any trailing bytes are
  ignored (the Rust runner appends a nonce so repeated vectors are distinct transactions).
-/
import LeanSVM
import Lemma.Math.ConstantProduct

open LeanSVM Lemma.Math

namespace LemmaTest.ChainProbes

abbrev ERR_MISMATCH : UInt64 := Err.custom 0xBAD

/-- ix: a, b, d (u64), mode (u8 @24), c (u64 @25). -/
def mulDiv (input : Ptr) : SolanaM Unit := do
  let (ix, _) ← Input.parse0 input
  SolanaM.require (ix.len >= 33) Err.invalidInstructionData
  let a ← loadU64 ix.ptr 0
  let b ← loadU64 ix.ptr 8
  let d ← loadU64 ix.ptr 16
  let mode ← loadU8 ix.ptr 24
  let c ← loadU64 ix.ptr 25
  let q ← if mode == 0 then mulDivFloorM a b d else mulDivCeilM a b d
  SolanaM.require (q == c) ERR_MISMATCH

/-- ix: reserveIn, reserveOut, amountIn, feeBps, c (u64 each). -/
def swap (input : Ptr) : SolanaM Unit := do
  let (ix, _) ← Input.parse0 input
  SolanaM.require (ix.len >= 40) Err.invalidInstructionData
  let x ← loadU64 ix.ptr 0
  let y ← loadU64 ix.ptr 8
  let amt ← loadU64 ix.ptr 16
  let fee ← loadU64 ix.ptr 24
  let c ← loadU64 ix.ptr 32
  let out ← swapOutM x y amt fee
  SolanaM.require (out == c) ERR_MISMATCH

/-- ix: a, b, c (u64). Exercises LEMMA patch 0001 on the real VM: `a + b` over `Nat` must be
    exact, or the program must abort (Solana `abort` syscall) when it overflows. -/
def natAdd (input : Ptr) : SolanaM Unit := do
  let (ix, _) ← Input.parse0 input
  SolanaM.require (ix.len >= 24) Err.invalidInstructionData
  let a ← loadU64 ix.ptr 0
  let b ← loadU64 ix.ptr 8
  let c ← loadU64 ix.ptr 16
  SolanaM.require (a.toNat + b.toNat == c.toNat) ERR_MISMATCH

end LemmaTest.ChainProbes
