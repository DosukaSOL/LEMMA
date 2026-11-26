/-
  LemmaTest.MathProbes — entrypoints that expose `Lemma.Math` functions to the interpreter.
  Input: `a @0, b @8, d @16 : u64`, `mode @24 : u8` (0 = floor, 1 = ceil), `c @32 : u64`.
  Returns 0 iff the on-chain function returns `c`; otherwise its error code (division by zero:
  `LErr.divByZero`; result does not fit: `Err.arithmeticOverflow`), or `Err.invalidArgument` if
  `ERR_MISMATCH` if it returned a value different from `c`.
-/
import LeanSVM
import Lemma.Math.ConstantProduct

open LeanSVM Lemma.Math

namespace LemmaTest.MathProbes

/-- Probe-only code: "the function succeeded but returned a different value". -/
abbrev ERR_MISMATCH : UInt64 := Err.custom 0xBAD

def p_mulDiv (input : Ptr) : SolanaM Unit := do
  let a ← loadU64 input 0
  let b ← loadU64 input 8
  let d ← loadU64 input 16
  let mode ← loadU8 input 24
  let c ← loadU64 input 32
  let q ← if mode == 0 then mulDivFloorM a b d else mulDivCeilM a b d
  SolanaM.require (q == c) ERR_MISMATCH

/-- `reserveIn @0, reserveOut @8, amountIn @16, feeBps @24, c @32`. -/
def p_swap (input : Ptr) : SolanaM Unit := do
  let x ← loadU64 input 0
  let y ← loadU64 input 8
  let amt ← loadU64 input 16
  let fee ← loadU64 input 24
  let c ← loadU64 input 32
  let out ← swapOutM x y amt fee
  SolanaM.require (out == c) ERR_MISMATCH

end LemmaTest.MathProbes
