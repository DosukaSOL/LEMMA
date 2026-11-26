# Patch 0001: sound `Nat` lowering

| | |
|---|---|
| **File** | `LeanSVM/Compiler/Lower.lean` |
| **Diff** | [`0001-sound-nat-lowering.patch`](0001-sound-nat-lowering.patch) (against upstream `d49665eac029d0a53a8f8fc324d840df6e9649d5`) |
| **Severity** | Soundness: compiled code could disagree with the Lean definitions that proofs are about |
| **Effect on upstream examples** | None: all 8 example `.so` files are byte-identical before and after |

## The bug

Upstream lowered `Nat` arithmetic to **wrapping 64-bit** sBPF instructions and truncated `Nat`
literals modulo 2^64:

| Lean | Upstream sBPF | Disagreement |
|---|---|---|
| `Nat.add a b` | `add64` | wraps instead of growing |
| `Nat.mul a b` | `mul64` | wraps |
| `Nat.sub a b` | `sub64` | wraps instead of saturating at 0 |
| `Nat.div a 0` | `div64` | traps instead of returning 0 |
| `Nat.mod a 0` | `mod64` | traps instead of returning `a` |
| literal `2^64` | `0` | silently truncated |
| `UInt32.ofNatTruncate n` | `n &&& 0xFFFFFFFF` | masks instead of clamping |

The compiler accepted these programs without warning. Minimal reproduction:

```lean
def t (input : Ptr) : SolanaM Unit := do
  let v ← rawLoadU64 input
  SolanaM.require (v.toNat * v.toNat > 2^64) Err.invalidArgument
```

Upstream compiles this to `mul64 r1, r1; jgt r1, 0, ok`. For `v = 3`, Lean's semantics say the check
fails (9 ≤ 2^64). The binary accepts it. Any theorem about a `Nat` computation therefore said
nothing about the deployed program.

## The fix

Every `Nat` value in a register is now the exact mathematical value (always `< 2^64`), or the
program has aborted:

| Lean | Patched lowering | Agrees with Lean? |
|---|---|---|
| literal `n` | `n` if `n < 2^64`, else **compile error** | exact |
| `Nat.add a b` | `r = a + b`; abort if `r < a` | exact, or aborts on overflow |
| `Nat.mul a b` | `r = a * b`; if `a ≠ 0` and `r / a ≠ b`, abort | exact, or aborts on overflow |
| `Nat.sub a b` | `a < b ? 0 : a - b` | exact |
| `Nat.div a b` | `b = 0 ? 0 : a / b` | exact |
| `Nat.mod a b` | `b = 0 ? a : a % b` | exact |
| `Nat.pow` | constant-folded when both operands are literals, otherwise compile error | exact |
| `UIntN.ofNatTruncate` | clamp to `2^N − 1` | exact |

"Abort" uses Solana's `abort` syscall, which ends the whole instruction even inside an outlined
helper. A bare `exit` there would only return to the caller.

So the compiled program **refines** the Lean program: on every input it either produces the same
result or aborts the transaction. An abort can never move funds or write state.

## How it is verified

1. **Scheme proofs (kernel-checked, standard axioms only).** [`Lemma/Compiler/NatLowering.lean`](../Lemma/Compiler/NatLowering.lean)
   proves that each check-and-compute scheme above computes exactly Lean's `Nat` result when it
   doesn't abort, and aborts exactly when the true result is `≥ 2^64`.
2. **Differential tests.** [`tests/LemmaTest/NatTests.lean`](../tests/LemmaTest/NatTests.lean)
   compiles 9 probe programs with the real pipeline and runs them in an independent sBPF
   interpreter on 14×14 boundary values plus 300 random pairs each. That is 9,061 checks against an
   overflow-tracking reference model.
   - Patched compiler: **9,061 pass, 0 fail.**
   - Unpatched upstream compiler: **1,371 fail**, and the `2^64` literal compiles. So the suite
     does detect the bug.
3. **Regression.** All 60 upstream compiler-soundness theorems still check, and all 8 upstream
   example binaries are byte-identical.

## What is NOT verified

- That `Lower.lean` emits exactly the proven schemes. That is shown by tests and review, not by
  proof; the compiler itself is not verified end to end.
- Behaviour on the real Agave VM. The interpreter is a test oracle, not Agave. In particular, the
  `abort` syscall was not executed on LiteSVM in this environment because crates.io was
  unreachable. Re-run the LiteSVM suite before relying on it.
- Compute-unit cost of the added checks (one compare-and-branch per `add`; a compare, a divide and a
  branch per `mul`).

## Policy in LEMMA

LEMMA's own runtime code does not use `Nat` at all. It uses `UInt64` with explicit checked
operations and relates them to `Nat` specifications in proofs. This patch is a second layer of
protection for `Nat` that reaches compiled code through the SDK or through library inlining.
