/-
  Examples.Noop
  Absolute theoretical minimum Solana program written in Lean 4:
  Compiles to 2 sBPF instructions (`mov64 r0, 0; exit`), 16 bytes `.text`, 0 stack, 0 heap!
-/
import LeanSVM

open LeanSVM

namespace Examples.Noop

def entrypoint (_input : Ptr) : SolanaM Unit :=
  pure ()

/-- Formal proof: `Noop.entrypoint` always succeeds (`code = 0`) and never mutates VM state. -/
theorem noop_always_succeeds (input : Ptr) (s : SvmState) :
    SolanaM.runEntry (entrypoint input) s = (0, s) := by
  rfl

end Examples.Noop
