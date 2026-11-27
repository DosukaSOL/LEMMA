# Audit checklist: program × Solana security property

Each cell names the theorem (**P**), runtime check with attack test (**T**), or reason that covers
the item, or says plainly that it isn't covered. Theorems are described in
[`specs/README.md`](specs/README.md); attack tests are in `tests/LemmaTest/GuardTests.lean`.

> **Status.** Components completed so far: **fee splitter**. Still to come from the roadmap:
> escrow, vesting, multisig, staking and timelock. Their rows will be added as each one is
> completed, and a component counts as done only when its row is fully filled in. `GuardedCounter`
> is an example, not a component.

## `Lemma.Components.FeeSplitter`

**P** = theorem (`Lemma/Components/FeeSplitterProofs.lean`) · **T** = attack test, run on the
compiled binary *and* the Lean model (`tests/LemmaTest/FeeSplitterTests.lean`), most also on
LiteSVM (`svm-runner/src/bin/lemma.rs`).

| # | Property | Coverage |
|---|---|---|
| 1 | Signer checks on every authority | **P** `splitIx_spec` / `initIx_spec` (`Signer s auth`), plus the signer must equal the configured authority (`HasKey s auth (vault+offAuth)`) · **T** "authority did not sign", "signer is not the configured authority" |
| 2 | Owner checks on every account read as program data | **P** `OwnedBy s vault progId` in both specs · **T** "vault owned by another program (spoofed config)". Recipients are never read as program data. |
| 3 | Writable checks | **P** vault (both specs) and all three recipients (`splitIx_spec`) · **T** "recipient read-only" |
| 4 | Account type discrimination | **P** `HasTag s vault TAG` in `splitIx_spec` · **T** "uninitialized vault". Recipients are identified by key, not by data. |
| 5 | Canonical PDA bumps; seeds documented | **Not applicable**: the vault is an ordinary program-owned account, not a PDA. |
| 6 | Re-initialization prevented | **P** `initIx_rejects_initialized` · **T** "re-initialization rejected" (also an attacker re-init on LiteSVM) |
| 7 | Duplicate mutable accounts rejected | **P** `NonDup` for all 5 slots in both specs, plus `requireDisjoint` on the four lamport fields · **T** "same recipient passed twice", "vault passed as a recipient" |
| 8 | Checked arithmetic; documented rounding | **P** `splitIx_spec`: exact shares (floor for recipients 1 and 2, remainder for recipient 0), dust ≤ 2 (`split_dust_bound`), checked adds and subs (`checkedAdd64_ok`/`checkedSub64_ok`), share-sum check immune to `u64` wrap (`validBps_toNat`) · **T** "share > 10000 (overflow trick)", "recipient balance would overflow u64", randomized differential (400 runs in the interpreter, 200 on LiteSVM) |
| 9 | CPI target program IDs verified | **Not applicable**: no CPIs; lamports move by direct debit and credit. |
| 10 | Account closing zeroes data, handles lamports | **Not applicable**: no close instruction. |
| 11 | Rent-exemption maintained | **P** `splitIx_spec`: the vault keeps at least `reserve`, and `initIx_spec` requires the vault to cover it at init. The deployer sets `reserve` to at least the vault's rent-exempt minimum; Agave rejects crediting rent-paying recipients, which the LiteSVM test respects. |
| 12 | No unbounded loops over user-controlled input | No loops in LEMMA code; account parsing is bounded by the runtime-supplied account count. |

**Also proven:** lamports are conserved across the four accounts (`splitIx_spec`). That is exactly
Agave's "balanced instruction" requirement, proven rather than left to runtime rejection.

## `Lemma.Examples.GuardedCounter`

| # | Property | Coverage |
|---|---|---|
| 1 | Signer checks on every authority | **P** `entrypoint_checks` (`Signer s (input+8)`) · **T** "missing signer" · stored authority must equal the signer: **T** "signer is not the stored authority" |
| 2 | Owner checks on every account read as program data | **P** `entrypoint_checks` (`OwnedBy s counter progId`) · **T** "counter owned by another program" |
| 3 | Writable checks | **P** `entrypoint_checks` (`Writable s counter`) · **T** "counter passed read-only" |
| 4 | Account type discrimination | **P** `entrypoint_checks` (`HasTag s counter TAG`) · **T** "wrong account kind", "data too short for a tag" |
| 5 | Canonical PDA bumps; seeds documented | **Not applicable**: no PDAs. **Gap for future components**: lean-svm has no PDA-derivation syscall binding (see trusted-base §5). |
| 6 | Re-initialization prevented | **Not applicable**: no initialize instruction. An uninitialized (zeroed) account is rejected: **T** "uninitialized (zeroed) counter". |
| 7 | Duplicate mutable accounts rejected | **P** `entrypoint_checks` (`NonDup` for both slots) · **T** "authority passed twice" |
| 8 | Checked arithmetic; documented rounding | `checkedAdd64` on the increment · **T** "counter overflow (u64::MAX)". No division, so no rounding. |
| 9 | CPI target program IDs verified | **Not applicable**: no CPIs. |
| 10 | Account closing zeroes data, handles lamports | **Not applicable**: no close instruction. |
| 11 | Rent-exemption maintained | **Not applicable**: lamports and data length never change (data length is checked to be exactly 48). |
| 12 | No unbounded loops over user-controlled input | The only loop is lean-svm's `skipAccounts` over the account count, which the runtime bounds. No LEMMA loop iterates over user input. |

## Library functions (not programs)

| Function | Arithmetic | Rounding |
|---|---|---|
| `mulDivFloorM` / `mulDivCeilM` | 128-bit intermediate; fails, never wraps (**P** `*_ok_iff`) | Explicit floor or ceil (**P** `*_bounds`) |
| `fpMulM` / `fpDivM` | Inherited from `mulDiv` | Caller chooses; **P** `fp*_bounds` |
| `swapOutM` | Checked add; `mulDiv` | Fee rounds up and output rounds down, both in the pool's favour (**P** `swapOutM_*_rounds_for_pool`) |
