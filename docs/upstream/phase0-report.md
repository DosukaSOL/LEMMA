# Phase 0: reconnaissance of upstream lean-svm

**Upstream:** `aeyakovenko/lean-svm` at `d49665eac029d0a53a8f8fc324d840df6e9649d5` (the only
commit at the time). **Toolchain:** `leanprover/lean4:v4.36.0`. Everything below was checked by
running it, not taken from the upstream README.

## What works

| Check | Result |
|---|---|
| `lake build` | Passes: 73 jobs, about 45 s. |
| Compile all 8 examples to `.so` | All compile, and sizes match the upstream README byte-for-byte (`noop` 352 B … `lending` 12,320 B). |
| LiteSVM runner (`svm-runner`) | **Not run in the reconnaissance environment**: crates.io was unreachable there. LEMMA's CI runs it. |
| `sorry` / explicit `axiom` | None. |

## Axiom audit (all 621 theorems in `LeanSVM.*` and `Examples.*`)

- 585 use only `propext` / `Classical.choice` / `Quot.sound`.
- **36 depend on `bv_decide` native-evaluation axioms**, including
  `vault_transfer_conserves_lamports`, `counter_increment_adds_one`,
  `lending_initObligation_zero_inits_dirty_mem`, `mulDiv64_ok_spec`, `mulDiv64Ceil_ok_spec`,
  `pushRawInsn_roundtrip` and the core `SvmState` memory lemmas. The live list is regenerated in
  [`../specs/axiom-report.md`](../specs/axiom-report.md).

The README's "zero custom axioms" is technically true, since these axioms are generated
automatically, but it hides the dependency on native code.

## Compiler feature support (tested with probe programs)

| Feature | Status |
|---|---|
| Structures | Supported (flattened into registers) |
| Tail recursion | Supported (becomes a loop) |
| Typeclasses | Supported (specialised away) |
| Non-tail recursion | Rejected with a clear error |
| `Array`, `List` | Rejected with a clear error |
| `Nat` arithmetic | **Accepted but miscompiled** (wraps at 2^64). Fixed by LEMMA patch 0001. |
| `Option` / sum values through join points | **Accepted but miscompiled** (payload replaced by 0). LEMMA patch 0002 turns this into a compile error. |
| Tuple-valued tail-recursive loop exit | Rejected with an error. |

## Account validation in the SDK

- Signer, writable and owner checks are explicit helper calls. Nothing is enforced automatically.
- `nextCursor` handles duplicate-account entries by advancing 8 bytes, but the accessors then read
  the 8-byte marker as if it were a full account. For example, `keyPtr` lands in the next slot's
  bytes. Programs must reject or resolve duplicates themselves. LEMMA's `requireNonDup` does this.
- **No PDA-derivation syscall bindings.** Programs receive a bump as input and can sign with it,
  but can't verify that it is canonical on-chain.
- Program-id pinning for SPL Token / Token-2022 / System CPIs exists (`checkTokenProg` etc.).

## Model fidelity

The `SvmState` model gives syscalls placeholder semantics: `sysMemcmp` compares one byte,
`sysSha256` doesn't hash, and `sysInvokeSignedC` always succeeds. Proofs that go through them don't
describe the real syscalls.

## Disconnected models in the examples

`amm_swap_preserves_k`, `amm_swap_never_drains_reserve`, `curve_buy_preserves_k`,
`curve_sell_bounded_by_reserve`, `dutchPrice_bounded`, `dutchPrice_monotone` and
`lending_healthy_cannot_be_liquidated` are stated about `Nat` model functions (`calcSwapOut`,
`calcBuyTokens`, `calcSellSol`, `dutchPriceNat`, `isHealthyNat`) that **no entrypoint calls**. The
deployed code reimplements the math with `mulDiv64` on `UInt64`. These theorems don't constrain the
deployed programs. LEMMA's equivalents (`swapOutM_*`) are stated about the on-chain function itself.

## Deployment targets

Output is a plain sBPF v0 ELF (`--sbpf v3` is optional). Execution on a real validator and
deployment via the upgradeable loader were **not verified**. LEMMA deploys only to LiteSVM and
localnet.

## Decision

LEMMA builds directly on a fork of lean-svm, because the user asked for a fork. Upstream files stay
in place so the fork can still merge from upstream. Compiler changes are minimal, each one is
documented in `patches/` with a diff, rationale and tests, and the 8 upstream example binaries are
byte-identical after every patch.
