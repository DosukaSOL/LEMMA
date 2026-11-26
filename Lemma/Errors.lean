/-
  Lemma.Errors — LEMMA's custom program error codes.

  Solana encodes `ProgramError::Custom(n)` as `n` in the low 32 bits of the exit code; built-in
  errors use the high 32 bits (see `LeanSVM.Err`). LEMMA custom codes share the prefix
  `0x4C4D____` ("LM") so they are recognisable in logs.
-/
import LeanSVM

namespace Lemma.LErr
open LeanSVM

/-- Division by zero requested (e.g. `mulDiv` with `d = 0`). -/
abbrev divByZero : UInt64 := Err.custom 0x4C4D0001

end Lemma.LErr
