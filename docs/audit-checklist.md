# Audit checklist: program × Solana security property

Each cell names the theorem (**P**), runtime check with attack test (**T**), or reason that covers
the item, or says plainly that it isn't covered. Theorems are described in
[`specs/README.md`](specs/README.md); attack tests are in `tests/LemmaTest/GuardTests.lean`.

> **Status.** The only LEMMA *program* so far is the `GuardedCounter` example. The component
> programs from the roadmap (escrow, vesting, multisig, staking, fee splitter, timelock) **have not
> been built yet**. Their rows will be added as each one is completed, and a component counts as
> done only when its row is fully filled in.

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
