<!--
  Draft issue for aeyakovenko/lean-svm. Not filed automatically; the maintainer of this fork
  decides whether to file it.
-->

# `Nat` arithmetic is lowered to wrapping 64-bit ops, so compiled code can disagree with proofs

**Commit:** `d49665eac029d0a53a8f8fc324d840df6e9649d5`

## Summary

`LeanSVM/Compiler/Lower.lean` maps `Nat.add/sub/mul/div/mod` to `add64/sub64/mul64/div64/mod64`, and
`valToReg` truncates `Nat` literals with `n.toUInt64`. Lean's `Nat` is unbounded and `Nat.sub`
saturates at zero, so any program whose `Nat` values reach 2^64, or that subtracts below zero, is
silently miscompiled. Theorems proven about such code do not hold for the binary.

## Reproduction

```lean
import LeanSVM
open LeanSVM
def t (input : Ptr) : SolanaM Unit := do
  let v ← rawLoadU64 input
  SolanaM.require (v.toNat * v.toNat > 2^64) Err.invalidArgument
```

`lake exe lean-svm build Repro Repro.t -o t.so --dump-asm` produces:

```
ldxdw r1, [r1+0]
mul64 r1, r1
jgt r1, 0, bb2      ; 2^64 was truncated to 0
```

For `v = 3`, Lean evaluates the condition to `false`, but the binary succeeds.

`UInt{8,16,32}.ofNatTruncate` has a related problem: it is lowered as a mask, but it should clamp.

## Impact on the bundled examples

None of the 8 examples is affected at runtime; their binaries don't change under a fix. But
`amm_swap_preserves_k`, `curve_buy_preserves_k`, `dutchPrice_*` and `lending_healthy_cannot_be_liquidated`
are stated about `Nat` model functions that the entrypoints don't call. They don't constrain the
deployed code, which reimplements the math with `mulDiv64` on `UInt64`.

## Suggested fix

Lower `Nat` ops as exact-or-abort: overflow-checked `add`/`mul` that call the `abort` syscall,
saturating `sub`, `div`/`mod` that special-case zero, and a compile error for literals `≥ 2^64`. A
tested implementation with kernel-checked lemmas for each scheme is available in the LEMMA fork
(`patches/0001-sound-nat-lowering.md`).

## Also noted

36 theorems, including `vault_transfer_conserves_lamports` and `mulDiv64_ok_spec`, depend on
`bv_decide`'s native-evaluation axioms (`*._native.bv_decide.ax_*`). That means they trust the
compiled LRAT checker, not only the kernel. This may be acceptable, but the README's "zero custom
axioms" doesn't make it visible.
