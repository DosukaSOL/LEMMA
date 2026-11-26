<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="assets/lemma-wordmark-dark.svg">
    <img alt="LEMMA" src="assets/lemma-wordmark-light.svg" width="420">
  </picture>
</p>

<p align="center">
  <b>Formally verified Solana programs, written and proven in Lean 4.</b><br>
  Machine-checked guarantees about the code that actually runs on-chain, not about a separate model.
</p>

<p align="center">
  <a href="../../actions/workflows/ci.yml"><img alt="CI" src="../../actions/workflows/ci.yml/badge.svg"></a>
  <img alt="Lean v4.36.0" src="https://img.shields.io/badge/Lean-v4.36.0-0B1020">
  <img alt="Proofs: kernel-checked, no sorry" src="https://img.shields.io/badge/proofs-kernel--checked%2C%20no%20sorry-E39B1F">
  <img alt="Status: unaudited" src="https://img.shields.io/badge/status-unaudited%20%C2%B7%20experimental-B42318">
</p>

> [!WARNING]
> **Unaudited, experimental research software built on a prototype compiler.** Don't use it with
> real funds or deploy it to mainnet until it has been independently audited. Nothing in this
> repository deploys to mainnet. See [SECURITY.md](SECURITY.md).

---

## What is LEMMA?

LEMMA is a toolkit for writing Solana programs whose safety properties are **proven** by the Lean
kernel. It builds on [lean-svm](https://github.com/aeyakovenko/lean-svm), which compiles Lean 4
directly to sBPF with no LLVM, no heap and no C runtime. That means a program and the theorems about
it are the same Lean code.

The core rule is that **a proof must constrain the deployed entrypoint, not a disconnected model.**
To make that rule hold, LEMMA checks the compiler as well as proving the programs:

- every LEMMA program is compiled and **differentially tested** against its own Lean definition,
  and against exact-integer references, on tens of thousands of inputs;
- the same compiled binaries run on **LiteSVM** (Agave) in CI;
- the proof base is audited mechanically on every commit.

### Fixed in lean-svm

Differential testing found **two silent miscompilations** in upstream lean-svm. In both, the
compiled program computed something different from the Lean code that had been proven correct:

| | Bug | Fix |
|---|---|---|
| [**Patch 0001**](patches/0001-sound-nat-lowering.md) | `Nat` arithmetic was lowered to *wrapping* 64-bit ops and literals were truncated (`2^64 → 0`), so any theorem about `Nat` code said nothing about the binary. | Every `Nat` operation is now exact or aborts the transaction. Each check is backed by a kernel-checked lemma. |
| [**Patch 0002**](patches/0002-no-silent-payload-loss.md) | An `Option`/sum value flowing through a join point silently lost its payload (`some q` read back as `0`), giving 6,978 wrong results in our suite. | Now a compile error instead of a miscompile. |

Both patches leave all 8 upstream example binaries **byte-identical**, and come with regression tests
that fail on the unpatched compiler. Reconnaissance also showed that 36 upstream theorems rely on
`bv_decide` native-code axioms, and that several headline example theorems are about functions the
deployed entrypoints never call. Details are in the [Phase 0 report](docs/upstream/phase0-report.md)
and a [draft upstream issue](docs/upstream/issue-nat-miscompilation.md).

### Built on top

| | What | Guarantees (all kernel-checked, standard axioms only) |
|---|---|---|
| 🧮 **`Lemma.Math`** | 128-bit `mulDiv` (floor/ceil), fixed point, constant-product swap | `mulDiv` returns `some q` **iff** the exact rounded result fits, so it never overflows silently. For the swap, proven on the on-chain function itself: **k never decreases**, **output < reserve**, and **every rounding favours the pool**. |
| 🛡️ **`Lemma.Spec` + `Lemma.Guard`** | Account-validation predicates and runtime checks | Each check succeeds **exactly when** its predicate holds (signer, writable, owner, key, kind tag, not a duplicate slot), and `guard_bind_ok` lifts that through a whole program. |
| 🎯 **Entrypoint theorems** | [`GuardedCounter`](Lemma/Examples/GuardedCounter.lean) example | `entrypoint_checks`: whenever the deployed entrypoint succeeds, every account check held. |
| 🔬 **sBPF test interpreter** | An independent executor for compiled programs | Model-vs-binary differential tests, plus 12 attack scenarios that must be rejected. |
| 📐 **Test vectors** | [`vectors/*.json`](vectors), 10k cases from the integer specification | Replay them against *any* implementation (Rust, TypeScript, …). |
| 🔒 **Proof-integrity audit** | `lake exe lemma-audit` | Fails on `sorry`, custom or native axioms, or `Nat` reachable from on-chain code. |

**Verified on the real SVM (LiteSVM, in CI):** all 10,032 JSON vectors pass against the compiled
programs (`mulDiv` ≤ 1,293 CU, swap ≤ 2,490 CU); every `GuardedCounter` attack is rejected (an honest
call costs 72 CU, in a 1,216-byte `.so`); and an overflowing `Nat` addition aborts on Agave instead
of wrapping, as patch 0001 requires.

Every theorem has a plain-English statement in [`docs/specs/`](docs/specs/README.md), and everything
that is **trusted rather than proven** is listed in [`trusted-base.md`](docs/specs/trusted-base.md).

## Status

| Component | Status |
|---|---|
| Phase 0: upstream audit | ✅ [Report](docs/upstream/phase0-report.md) |
| Compiler soundness patches | ✅ 2 patches, with tests |
| Repo skeleton, CI, secret scanning, supply-chain pinning | ✅ |
| `Spec/` safety predicates and proven guards | ✅ |
| **2. DeFi math library** | 🟡 Done: `mulDiv`, fixed point, constant-product swap, JSON vectors. To do: StableSwap solver, interest-rate curves, oracle/decimals conversion, liquidation checks. |
| **1. Component library** (escrow, vesting, multisig, staking, fee splitter, timelock) | ⬜ Not started. The validation layer and entrypoint-proof pattern they will use is in place (`GuardedCounter`). |
| **4. Differential harness** | 🟡 Lean model vs compiled binary in the interpreter, and on LiteSVM in CI. To do: Rust reference implementations with property-based fuzzing. |
| **3. IDL + TypeScript client generator** | ⬜ Not started |
| **6. Size/CU benchmark suite** | ⬜ Not started (upstream's benchmarks still run in CI) |
| **5. Spec-first AI scaffolding tool** | ⬜ Not started |

## Quick start

```bash
# Toolchain: the exact Lean release, verified by SHA-256 (or use elan with lean-toolchain)
export PATH="$(scripts/install-lean.sh):$PATH"

lake build Lemma LemmaTest lean-svm lemma-test lemma-audit lemma-vectors   # build + check every proof
lake exe lemma-audit        # axiom policy + runtime-Nat lint (fails if docs/specs/axiom-report.md is stale)
lake exe lemma-vectors      # fails if vectors/*.json are stale
lake exe lemma-test         # differential, vector and attack suites in the sBPF interpreter
scripts/build-programs.sh   # compile every program to build/*.so

# Real SVM (needs crates.io access):
cargo run --locked --release --manifest-path svm-runner/Cargo.toml --bin lemma
```

Optional: `scripts/install-hooks.sh` enables the gitleaks and proof-hole pre-commit hook.

## How the guarantees fit together

```
 Lean definition ──(theorems, Lean kernel)──▶  proven properties of the on-chain function
       │
       ├──(lean-svm + LEMMA patches)──▶ sBPF .so ──┬─▶ LEMMA interpreter: must agree with the Lean
       │                                          │   definition / Nat reference / JSON vectors
       │                                          └─▶ LiteSVM (Agave) in CI: same vectors and attacks
       └──(lemma-audit)──▶ only standard axioms · no sorry · no Nat in on-chain code
```

The compiler is not verified end to end. Differential testing narrows that gap but doesn't close it;
see the [trusted base](docs/specs/trusted-base.md).

## Repository layout

```
Lemma/
  Compiler/NatLowering.lean   lemmas behind compiler patch 0001
  Math/                       Wide (128-bit), MulDiv, FixedPoint, ConstantProduct, Witnesses
  Spec/Accounts.lean          account-validation predicates
  Guard.lean                  runtime checks proven equivalent to the predicates
  Examples/GuardedCounter.lean  end-to-end example with an entrypoint-level theorem
tests/
  LemmaTest/                  sBPF interpreter, ABI serializer, differential / vector / attack suites
  LemmaAudit/                 proof-integrity audit
  LemmaVectors/               JSON vector generator
svm-runner/src/bin/lemma.rs   the same checks on LiteSVM
patches/                      every change to upstream compiler code, with rationale and tests
vectors/                      reference test vectors (generated)
docs/                         specs, trusted base, audit checklist, upstream findings
LeanSVM/ Examples/ ...        upstream lean-svm (unchanged apart from patches/)
```

## Contributing

Every change must keep `lake exe lemma-audit` and `lake exe lemma-test` green. Every theorem gets a
plain-English entry in `docs/specs/README.md`, and every program gets a full row in
`docs/audit-checklist.md`. Changes to upstream compiler code go in a new numbered file in `patches/`,
with a regression test that fails without the patch.

## Security

Please report vulnerabilities privately; see [SECURITY.md](SECURITY.md). Reports of a miscompilation,
a vacuous theorem, or a statement that doesn't mean what its documentation says are especially
welcome.

## License

LEMMA's own contributions are licensed under [Apache-2.0](LICENSE). Upstream lean-svm files had no
license at the forked commit and are **not** covered; see [NOTICE](NOTICE).

## Acknowledgements

Built on [lean-svm](https://github.com/aeyakovenko/lean-svm) by Anatoly Yakovenko, and on
[Lean 4](https://lean-lang.org). The original lean-svm README is preserved in
[`docs/upstream/lean-svm-README.md`](docs/upstream/lean-svm-README.md).
