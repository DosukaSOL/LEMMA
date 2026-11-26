<!--
  Draft issue for aeyakovenko/lean-svm. Not filed automatically; the maintainer of this fork
  decides whether to file it.
-->

# Two silent miscompilations: wrapping `Nat` arithmetic, and dropped constructor payloads

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

## Second bug: constructor payloads are silently dropped (`valToReg`)

For a constructor with a tag other than 0 and a runtime field, `valToReg` returns only the tag. So an
`Option.some q` (or any sum value) that flows through an `if` join point or a multi-branch return
loses `q`, and `q` later reads as `0`:

```lean
let r := if mode == 0 then mulDivFloor a b d else mulDivCeil a b d   -- Option UInt64
match r with
| none => SolanaM.fail 7
| some q => SolanaM.require (q == c) Err.invalidArgument
```

The generated code compares `c` against the constant `0`. In differential testing this pattern gave
6,978 wrong results for functions whose Lean definitions are proven correct. `dynCtor` values have
the same problem. A safe fix is to make this a compile error (LEMMA patch 0002); proper multi-register
join parameters would be the full feature.

## Also noted

36 theorems, including `vault_transfer_conserves_lamports` and `mulDiv64_ok_spec`, depend on
`bv_decide`'s native-evaluation axioms (`*._native.bv_decide.ax_*`). That means they trust the
compiled LRAT checker, not only the kernel. This may be acceptable, but the README's "zero custom
axioms" doesn't make it visible.

**Licence file (separate, minor):** the `LICENSE` added in `2e36957` isn't the verbatim
Apache-2.0 text. Several clauses are worded differently from the official version at
<https://www.apache.org/licenses/LICENSE-2.0>, e.g. §5 ("without any warranty of any kind"
instead of "without any additional terms or conditions"), §4(c), §8 and §9. You may want to
replace it with the official text so the terms are unambiguous.
