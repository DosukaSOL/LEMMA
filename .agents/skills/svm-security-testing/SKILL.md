---
name: svm-security-testing
description: >-
  Security audit, formal proof, and LiteSVM adversarial testing guide for Solana
  programs built with lean-svm. Use whenever designing, reviewing, hardening, or
  testing a lean-svm program to catch common SVM and real-world mainnet bugs
  (same-tx account revival, dirty-buffer init, missing owner/size/discriminator
  checks, spoofed CPI programs, SPL/lamport self-transfer aliasing, share-pool
  inflation, K=4 adversarial leader censorship & compounding bounds, cross-market
  stale-oracle DoS, Dutch-auction 1-atom dust-reset & batch clearing, Token-2022
  TransferFee / wSOL burn traps, and proof-to-runtime / compiler gaps).
---

# SVM Security Testing & Hardening Guide (`lean-svm`)

Pure mathematical (`Nat`) proofs verify economic formulas, **not** Solana's binary account ABI, CPI dispatch, or transaction lifecycle. A bug at the SVM boundary (dirty account memory, unpinned CPI program ID, same-tx rent refund) can bypass every pure-math invariant without violating a single `Nat` theorem.

Use this checklist whenever writing, reviewing, or testing any `lean-svm` program.

---

## Core Principle: SVM Abort Semantics

- **Error paths need zero cleanup:** When a Solana instruction returns a nonzero error code (`SolanaM.fail` / failed `SolanaM.require`), the SVM discards **all** account and lamport mutations across the entire transaction. Never spend CUs zeroing or rolling back state before returning an error.
- **Success paths persist within the transaction:** Any account mutated by a *succeeding* instruction — including an account drained to `0` lamports — remains alive with its exact bytes for subsequent instructions in the **same transaction**. Garbage collection only happens at the end of the transaction if lamports are still `0`.

---

## Vulnerability Classes, `lean-svm` Fixes, Proofs & LiteSVM Tests

### 1. Same-Tx Account Revival & Cross-Type Confusion

**The Bug:**
A `CloseAccount` instruction sets only the 4-byte discriminator/magic to `0` and drains lamports to `dest`. In the **same transaction**, an attacker appends:
1. `CloseAccount(acc)` → sets `data[0..4] = 0`, `lamports = 0`, leaves bytes `4..N` intact.
2. `SystemProgram::Transfer(attacker → acc, rent)` → prevents end-of-tx garbage collection!
3. `InitOtherType(acc)` → sees `magic == 0` and `dataLen >= otherSize`, skips zeroing fields it assumes are `0`, and inherits residual bytes from the previous type (e.g., an owner pubkey overlapping a `shares` or `capital` `u64`!).

**How to Prevent (`lean-svm`):**
1. Write a **permanent nonzero tombstone magic** on close (e.g., `MAGIC_CLOSED : UInt32 := 0x44454144`), distinct from `0` and every live magic, so neither live handlers nor fresh-init (`magic == 0`) branches can ever accept a closed account.
2. Enforce **exact** `dataLen == exactSize` (never `>=`) on every account check and init path, and give distinct account types distinct sizes where practical.
3. Call `LeanSVM.CPI.zeroWords (AccountView.dataPtr acc) 0 (size >>> 3)` on **both** fresh initialization and close (defense-in-depth; costs ~5 CUs per 8-byte word on one-time init/close, **0 CU on hot paths**).

**Formal Proof Pattern (`SvmState.mem`):**
- Use `LeanSVM.CPI.zeroWords_exact` + `LeanSVM.CPI.bind_ok_elim` to prove:
  1. Closing writes `MAGIC_CLOSED ≠ 0`, distinct from all live magics, and zeroes `[4, size)`.
  2. Fresh initialization from **arbitrary dirty `SvmState.mem`** always yields `0` for all balance/share/debt fields (see `Examples.Lending.lending_initObligation_zero_inits_dirty_mem`).

**LiteSVM Test Recipe:**
```rust
// Single atomic transaction: [CloseAccount(acc), SystemTransfer(payer -> acc, rent), InitOtherType(acc)]
// Assert the tx FAILS!
// Also test [CloseAccount(acc), SystemTransfer(payer -> acc, rent)] alone, then inspect:
//   assert_eq!(&acc.data[0..4], &MAGIC_CLOSED.to_le_bytes());
//   assert!(acc.data[4..].iter().all(|&b| b == 0));
//   and verify a follow-up Init*(acc) in the next tx ALSO fails!
```

---

### 2. Dirty-Buffer Initialization

**The Bug:**
An initialization path checks `magic == 0` (or `initialized == 0` / `idx == 0`), writes header fields, and then updates a balance via `old + amount` without first zeroing the account body. If the account was pre-filled or previously used, `old` is nonzero garbage.

**How to Prevent:**
- Always call `zeroWords (AccountView.dataPtr acc) 0 (size >>> 3)` before writing initial fields, or explicitly store `0` to every single field (including padding and array slots).
- Never use a mutable business field (like `idx == 0` or `balance == 0`) as the initialization flag — use a dedicated immutable magic/discriminator byte or `u32`.

**LiteSVM Test Recipe:**
- Construct the fresh account in `svm.set_account(...)` with `magic == 0` (`data[0..4] = 0`) and **every other byte filled with `0xFF` or sentinel nonzero `u64` values** (e.g. `999_999_999` in balance/shares/collateral slots).
- Execute `Init` / first `Deposit` and assert every balance/counter equals the exact deposited amount (or `0`), with zero leaked sentinel bytes.

---

### 3. Missing Owner Pinning, Exact Size, or Discriminator Checks

**The Bug:**
Forgetting `pubkeyEq (AccountView.ownerPtr acc) progId`, checking `dataLen >= size` instead of `== size`, or omitting a type magic lets an attacker:
- Pass a **System-owned** (or attacker-program-owned) account populated with arbitrary forged balances/authority pubkeys.
- Pass an account of Type A into a handler expecting Type B.

**How to Prevent:**
Centralize a single `@[noinline]` validator per account type:
```lean
@[noinline] def checkMyAccount (acc : AccountView) (progId : Ptr) : SolanaM Unit := do
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr acc) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen acc) == MY_SIZE) Err.invalidAccountData
  SolanaM.require ((← loadU32 (AccountView.dataPtr acc) 0) == MAGIC_MY) Err.invalidAccountData
```

**Formal Proof Pattern:**
- Prove `rejects_wrong_owner`: if `acc.owner ≠ progId`, the handler returns `Err.illegalOwner` with `s' = s` (see `Examples.Counter.counter_rejects_wrong_owner`).

**LiteSVM Test Recipe:**
- Pass an account with identical valid data bytes but `owner: SYSTEM_PROGRAM_ID` → assert error.
- Pass a program-owned account with `data.len() == MY_SIZE + 8` (oversized) and `MY_SIZE - 8` (undersized) → assert error.
- Pass a valid initialized account of Type A where Type B is expected → assert error.

---

### 4. Arbitrary CPI / Spoofed Program ID (`noop.so` Attack)

**The Bug:**
A program invokes `tokenTransferChecked tokProg ...` or `systemTransfer sysProg ...` without verifying `tokProg` or `sysProg`'s 32-byte pubkey. An attacker deploys/passes a trivial executable `noop.so` (returns `0` immediately) as `tokProg` or `sysProg`: the CPI succeeds, no tokens/SOL move, and the program credits the attacker's internal balance for free.

**How to Prevent:**
Always pin every CPI target using `LeanSVM.CPI`:
- `checkSystemProg sysProg` (`11111111111111111111111111111111`)
- `checkTokenProg tokProg` (`TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA`)
- `checkTokenOr2022Prog tokProg` (SPL Token OR `TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb`)
- For custom downstream CPI targets, pin against the 32-byte pubkey stored in an immutable config account.

**Formal Proof Pattern:**
- Already proven in `LeanSVM.CPI`: `checkSystemProg_sound`, `checkTokenProg_sound`, `checkTokenOr2022Prog_sound`.

**LiteSVM Test Recipe:**
- Deploy `build/noop.so` at a fresh `Address::new_unique()` in LiteSVM.
- Call **every** instruction that performs a token or system CPI with `fake_prog` in place of `SPL_TOKEN_ID` / `SPL_TOKEN_2022_ID` / `SYSTEM_PROGRAM_ID`.
- Assert **every single one** returns `Err`.

---

### 5. Account Aliasing & SPL / Lamport Self-Transfers

**The Bug:**
Two account arguments point to the same pubkey:
- **SPL Token self-transfer (`source == dest`):** Passing `vault` as `destTok` on withdrawal makes SPL Token execute a **no-op** (vault SPL balance unchanged) while the program still decrements its internal `vaultBalance` (`internal < SPL`, permanently orphaning tokens and breaking exact stock conservation).
- **Direct lamport self-transfer (`from == to`):** Reading both `fromBal` and `toBal` before writing (`setLamports from (bal - amt); setLamports to (bal + amt)`) overwrites the debit with `bal + amt` (or corrupts internal balances).
- **Two-party state aliasing (`pflA == pflB`, `vaultA == vaultB`):** Reading both balances, mutating both, and writing back loses the first write or lets a user trade/liquidate against themselves.
- **Solana ABI Duplicate-Account Markers (`dupMarker != 0xFF`):** When an instruction legitimately accepts two accounts that *may* share the same pubkey (e.g., `quoteTokProg` and `targetTokProg` both being `TOKEN_PROGRAM_ID`, or `quoteMint == targetMint`), Solana serializes the second occurrence as an **8-byte duplicate marker** (`byte 0 = original_index`, NOT `0xFF`). Calling `AccountView.keyPtr` / `dataPtr` directly on a duplicate `AccountView` reads garbage from the next account!

**How to Prevent:**
- Explicitly require `!(← pubkeyEq (AccountView.keyPtr a) (AccountView.keyPtr b))` for every pair of accounts that must be distinct (`userTok != vault`, `destTok != vault`, `liqTok != vault`, `from != to`, `partyA != partyB`, `acc != dest`), AND check `(← rawLoadU8 acc) == ABI.nonDupMarker` (`0xFF`) whenever an account must be non-duplicate.
- Whenever a later account is *allowed* to alias a known earlier account at index `k` (like `targetTokProg == quoteTokProg`), check `let dup ← rawLoadU8 acc; if dup != ABI.nonDupMarker then require (dup == k)` and resolve to the original `AccountView` before reading its key/owner/data!

**LiteSVM Test Recipe:**
- Pass `vault` as `destTok` on every withdrawal / fee payout → assert error.
- Pass `acc` as `dest` on `CloseAccount` and `from` as `to` on lamport transfers → assert error.
- Pass `partyA` for both sides of a bilateral trade / liquidation takeover → assert error.

---

### 6. CPI Proxy / Wrapper Forwarding Unvalidated Opcodes or Unpinned Targets

**The Bug:**
A wrapper/router/AMM program holds a PDA authority over an LP account and CPIs into a core program. If the wrapper:
- Forwards a user-supplied `mode` / `op` byte without allowlisting the exact modes its quoting/accounting logic expects (e.g., forwarding `mode = 2` hand-off when the wrapper's spread calculation only handles `mode = 0` open / `mode = 1` close), or
- Fails to pin the target `market` / `pool` / `mint` account in its config,

then a caller can force the wrapper's PDA to sign unintended operations or trade on an adversarial permissionless market.

**How to Prevent:**
- Allowlist every forwarded enum/mode explicitly (`SolanaM.require (mode == 0 || mode == 1) ...`).
- Pin every target account (`percProg`, `lpPortfolio`, `market`, `mint`) in the wrapper's immutable config.

**LiteSVM Test Recipe:**
- Call every wrapper instruction with every out-of-range / unexpected `mode` byte (`2, 3, 255`) and with a rogue permissionless market → assert error.

---

### 7. Share-Pool / Vault Accounting Footguns (ERC-4626 Class)

**The Bug:**
Pro-rata share pools (`minted = amount * totalShares / totalAssets`, `payout = burnShares * totalAssets / totalShares`) have four classic edge cases:
1. **Unclaimed assets before first LP (`totalShares == 0 && assets > 0`):** If fees or donations accrue before any LP deposits, depositing `1` unit mints 100% of shares and steals all prior fees/donations.
2. **Drained-pool share revival (`assets == 0 && totalShares > 0`):** If bad debt drains `assets` to `0` while old LPs keep `totalShares > 0`, a new LP minting 1:1 immediately donates `oldShares / (oldShares + new)` of their deposit to the wiped-out LPs.
3. **Donation inflation (`totalShares == 1` + large direct donation):** Inflates 1 share to huge value so honest deposits truncate (`minted == 0`) or lose value to rounding.
4. **Receipt-to-total desync (`receipt.shares > totalShares`):** Always guard `curSh <= totSh` on redemption and prove `totalShares = ∑ receipt.shares`.
5. **Trapped rent on closure:** Allowing permissionless pool tombstoning while receipts still hold nonzero worthless shares (`shares > 0`) permanently blocks LPs from closing their receipt accounts if `Withdraw` rejects tombstoned pools.

**LiteSVM Test Recipe:**
- Test all 4 boundary states explicitly:
  - `(totSh = 0, assets = 1_000_000)` → attempt `1`-unit deposit + withdraw.
  - `(totSh = 100_000, assets = 0)` → new LP deposits `10_000`, verify old LP cannot withdraw new LP's funds.
  - `(totSh = 1, assets = 1)` → donate `100_000_000` → second LP deposits `50_000_000` & `150_000_000`, assert attacker cannot profit.
  - Drain pool to `0` while LP holds shares → verify LP can still burn worthless shares and reclaim receipt rent.

---

### 8. Missing Signer, Writable, PDA Derivation & Pre-Funding Griefing

**The Bug:**
- Checking `owner == authority` without checking `AccountView.isSigner authority`.
- Creating a PDA via `SystemProgram::CreateAccount` — an attacker can send 1 lamport to the deterministic PDA address beforehand, permanently bricking `CreateAccount`.

**How to Prevent:**
- Always check `AccountView.isSigner` on every authority and `AccountView.isWritable` on every mutated account.
- Create PDAs on-chain using **`SystemProgram::Transfer` (top-up rent diff) + `systemAllocateSigned` + `systemAssignSigned`** (already in `LeanSVM.CPI`), which succeeds even if the PDA already holds lamports.

**LiteSVM Test Recipe:**
- Pre-fund the target PDA with `1` lamport before running `Init*` → assert `Init*` still succeeds!
- Omit `.is_signer = true` on every authority account in every instruction → assert error.

---

### 9. Stale Cross-Account State & Multi-Instruction Ordering

**The Bug:**
In multi-account / cross-margin protocols, allowing withdrawals, risk-increasing trades, spread transfers, or liquidations while *other* legs/positions on the same user are stale lets attackers either extract collateral before realizing losses or selectively liquidate a hedged user without crediting their winning legs.

**How to Prevent:**
- Stamp `lastRefreshSlot = curSlot` on every state refresh and enforce `lastRefreshSlot == curSlot` across all active positions before withdrawal, liquidation, or any collateral-reducing transfer (including spread payments).

**LiteSVM Test Recipe:**
- Advance `Clock.slot`, refresh only one leg, attempt `Withdraw`, `Liquidate`, and spread-paying `Trade` → assert all fail until every active leg is refreshed in the same slot.

---

### 10. Arithmetic Overflow, Underflow & Rounding Direction

**The Bug:**
- Unchecked `UInt64` `+` / `-` wrapping silently in sBPF.
- 64-bit `a * b / c` overflowing `2^64` on intermediate products.
- Rounding in favor of the user (floor on debt/margin/cost, ceil on payout/mint) allowing dust extraction loops.

**How to Prevent:**
- Use `checkedAdd64` / `checkedSub64` for every balance/supply/debt mutation.
- Use `LeanSVM.Math.mulDiv64` (floor, exact 128-bit) for user payouts/mints/swaps and `LeanSVM.Math.mulDiv64Ceil` (ceil, exact 128-bit) for margin requirements, fees, and debt/loss debits.
- Prove rounding direction in Lean 4 using `mulDiv64_ok_spec` / `mulDiv64Ceil_ok_spec`.

**LiteSVM Test Recipe:**
- Test `u64::MAX` overflow inputs on `Add`/`Deposit`/`Borrow` → assert error.
- Test 128-bit-requiring values (`a * b > 2^64`, e.g. `10^12 * 10^9 / 10^10`) → assert exact 128-bit result without wraparound.
- Run a randomized stateful fuzzer (500–1,000+ steps) asserting exact global stock conservation (`sum_internal == spl_vault_balance`) after **every** transaction.

---

### 11. Real-World Solana Mainnet Threat Model: `K = 4` Adversarial Leader Windows & Compounding Bounds

**The Bug:**
- Assuming a 1-slot rate limit or 1-slot delay stops an adversarial validator. On Solana mainnet, a single leader is scheduled for **`K = 4` consecutive slots** (~1.6s), and a colluding cartel / Jito bundle builder can censor competing liquidations or bids across `T` consecutive slots.
- Using a linear `4 * maxMoveBps` approximation for 4 consecutive price steps understates true compounding `((10_000 + m)^4 - 10_000^4) / 10_000^3` (e.g. `m = 100` bps gives `406.04` bps, NOT `400` bps — breaching `mmBps = 500` when `liqFeeBps = 100`!).
- Leaving `imBps - mmBps < maxMoveBps` allows a same-slot oracle update to push a freshly opened position straight past maintenance margin.

**How to Prevent:**
- Model the exact `K = 4` (or `T`-slot) adversarial-leader censorship window explicitly in your Lean `ThreatModel`.
- Enforce the exact compounded envelope at market/pool creation:
  - `k4MoveBps := 4 * maxMoveBps + (maxMoveBps * maxMoveBps + 999) / 1000` (proven `≥` exact 4-step compounding for all `m ≤ 2500`)
  - `k4MoveBps + liqFeeBps ≤ mmBps` AND `mmBps + maxMoveBps ≤ imBps`
- Never rely on `T = 1`-slot delays for liveness or auction clearing; any anti-censorship window (e.g. batch auction epoch or wind-down staleness) must satisfy `windowSlots ≫ K = 4` (e.g. `≥ 32` slots minimum, `750–2250` slots / 5–15 min in production).

**LiteSVM Test Recipe:**
- Test exact boundary rejection (`m = 100, mm = 500, liqFee = 100` → rejected; `m = 95` → accepted).
- Simulate 4 consecutive adversarial oracle steps with liquidations censored until slot 5, and assert `badDebt == 0` and `insDraw == 0`.

---

### 12. Permissionless Multi-Market Isolation & Stale-Oracle DoS

**The Bug:**
- **Stale-oracle cross-margin DoS:** In a multi-market cross-margin portfolio, if `RefreshLeg` requires `checkOracleFresh`, any permissionless or abandoned market can halt its oracle to permanently freeze `Withdraw` and `Liquidate` on *every* user holding a leg in that market (even on healthy BTC/ETH legs!).
- **Capital-shielding / partial-bankruptcy drain:** Reserving capital per-leg (`reservedMm`) so a loser triggers insurance draws while still holding `capital > 0`, OR allowing partial liquidation on a `capital == 0` bankrupt leg (leaving zombie bad debt).
- **Asymmetric post-ADL rounding & sub-nanounit dust:** After partial ADL (`oiSide < rawSide`), using floored `Δk` on the losing side under-collects relative to winners (`∑ gain > ∑ loss`), and a `>10^9:1` wipeout can leave `oi > 0` with `adl == 0` (an unclosable zombie leg).
- **Fronting / receivable NAV arbitrage:** When an insurance pool fronts USD to winners (`insFronted > 0`), pricing LP share mints on cash `ins` alone lets attackers mint cheap shares and capture incoming loser repayments.

**How to Prevent:**
- **Rule of thumb:** An unrelated adversarial permissionless market must **never** touch an honest user's PnL/capital, **never** touch another market's insurance/reward buckets, and **never** freeze another market's liveness.
- Do **not** call `checkOracleFresh` in `RefreshLeg` (a stale market has frozen `markPrice`, settles `ΔK = 0`, keeps its full `cachedMm`/`cachedIm` locked, and unblocks same-slot freshness on healthy legs).
- Settle losses against **full portfolio capital** (`shortfall > 0 ⇒ capital' == 0`), force full close when `capital == 0`, use ceiling `Δk` on the losing side vs floor `Δk` on the winning side, snap sub-nanounit dust OI (`adl' == 0`) cleanly to `0`, and price insurance LP mints on optimistic NAV (`ins + insFronted`) while bounding `maxFrontBps ≤ maxInsDrawBps`.

**LiteSVM Test Recipe:**
- Create an adversarial permissionless market, halt its oracle past `maxStaleness`, and verify a user with legs in both the stale market and a healthy market can still refresh, withdraw excess margin, and be liquidated cleanly.
- Verify an adversarial market's trades, liquidations, and reward claims leave every unrelated market's `insurance`, `realizedPool`, `rewardAccrued` and every unrelated user's `capital` bit-for-bit untouched.

---

### 13. On-Chain Auctions, Buybacks & Fee-Capture Anti-MEV / Anti-Spam Rules

**The Bug:**
- **1-Atom Dust-Reset / Rate-Inflation DoS (Naive Dutch Auctions):** Allowing any partial fill (`quoteAmt = 1`, $0.000001) to reset `epochStartSlot` and double `startRate` lets an attacker permanently pin the auction at `MAX_RATE` for pennies — or snipe 1 atom at the floor to ratchet the next epoch down to `minRate`.
- **Fixed Price-Floor Volatility Trap:** Immutable `minRate` permanently freezes funds if an external token pumps 100x, or drains value if the token dumps 100x.
- **Spam / Unfunded / Cancellable Bid DoS:** Any `O(N)` loop over bidder accounts in settlement hits Solana's 200k CU / 1232 B tx limit; any cancellable bid enables last-slot spoofing; pure pro-rata (`B_virt = 0`) lets a 1-atom bidder steal 100% of a quiet/censored epoch.
- **Extreme Dump `mulDiv64` Overflow DoS:** Computing `clearedRate = mulDiv64 B POS_SCALE Q` on settlement without pre-checking `B / Q >= 4 * (MAX_RATE_E6 / POS_SCALE)` overflows `UInt64` on a 1,000,000x token dump and bricks settlement!

**How to Prevent (Gavel-Style `xy = k` Virtual-Reserve X-Minute Uniform-Price Batch):**
- Separate **disjoint accounting buckets** (e.g. `DexOff.totalRewards` disjoint from `totalSurplus`, `totalInsurance`, `totalCapital`) so protocol admin sweeps can never touch per-market reward pools.
- Use fixed-duration epochs (`epochSlots ≥ MIN_EPOCH_SLOTS ≫ K = 4`), **irrevocable** AMM-style unlimited bids (`O(1)` per bid, `O(1)` settlement, `O(1)` claim across overlapping `EpochState` accounts), and uniform `xy = k` virtual-reserve clearing:
  - `quotePaid = floor(Q * B / (B + B_virt))`, `rollover = Q - quotePaid`, `payout_i = floor(Q * b_i / (B + B_virt))`.
  - Prove `∑ payout_i ≤ quotePaid ≤ Q` (guaranteed 100% claimable for unlimited bidders), `payout_i * B_virt ≤ Q * b_i` (1-atom quiet-epoch cap), and once-per-epoch self-calibrating `reserveRateE6` (halves on underfill → zero 1000x-pump freeze; clamps `B / Q` before `mulDiv64` → zero overflow DoS).

**LiteSVM Test Recipe:**
- Submit multiple bids from the same bidder (same receipt) + 5+ 1-atom dust spam bids across separate receipts; verify `SettleEpoch` is O(1) CU, honest bidders get the exact same uniform price, and 1-atom spammers receive `0` quote.
- Simulate a quiet/censored epoch with ONLY a 1-atom attacker bid; assert `quotePaid == 0`, 100% of `Q` rolls over intact into Epoch 2, and `reserveRateE6` halves.

---

### 14. External Token-2022 Extensions (`TransferFee`, `FreezeAuthority`) & `wSOL` NativeMint Burn

**The Bug:**
- **SPL `Burn` rejects `wSOL` (`So11111111111111111111111111111111111111112`)** with `NativeNotSupported`.
- **Token-2022 `TransferFee` inflation:** Crediting instruction `amount` instead of actual tokens arriving in the escrow causes later burns/withdrawals of `totalCredited` to revert with `InsufficientFunds` (permanent DoS or insolvency).
- **Mint `FreezeAuthority`:** A malicious or untrusted mint's freeze authority can freeze the program's vault/escrow, permanently DoS-ing all users.

**How to Prevent:**
- Support BOTH `burnMode = 0` (real SPL Token / Token-2022 `Burn` reducing `mint.supply`) AND `burnMode = 1` (transfer into a PDA-owned permanent dead-sink account with **zero** withdraw instruction) for `wSOL`.
- On every inbound transfer of an arbitrary external SPL / Token-2022 token, measure the **exact balance delta** (`received = postBal - preBal`) on the escrow account and credit strictly `received`.
- For core base-collateral vaults, forbid `freeze_authority != None` by default (with an explicit immutable opt-in `allowFreeze` flag for blessed issuer mints like USDC/USDT).

**LiteSVM Test Recipe:**
- Test real SPL Token, real **Token-2022**, AND real **wSOL** (`is_native = Some(rent)`) end-to-end in LiteSVM, verifying `mint.supply` decreases for SPL/Token-2022 and dead-sink balance increases for wSOL.

---

### 15. Compiler, Byte-Layout & Proof-to-Runtime Gap Discipline (`lean-svm`)

**The Bug:**
- Pure `Nat` proofs do not catch `UInt64` wraparound, ABI byte-offset typos, or sBPF codegen bugs (such as register-reuse clobbering when a binary instruction's destination aliases its RHS operand in lowering/regalloc).
- **Silent Trailing-Byte Truncation / Readonly `AccountDataTooSmall` (Agave Direct Mapping):** If a struct's `size` is accidentally smaller than `lastField + fieldWidth` (e.g. a 32-byte `Pubkey` at offset `368` with `size = 392` instead of `400`), writes to a **writable** account silently spill into Solana's 10KB realloc padding and get **silently truncated to zero** during serialization, while any **readonly** reader that reaches the trailing bytes faults with `InstructionError::AccountDataTooSmall` inside Agave's direct-mapping VM!

**How to Prevent:**
- Always add a compile-time `by decide` theorem in your `Layout` module proving `lastField + fieldWidth ≤ size ∧ size % 8 == 0` for every account struct — making off-by-N layout truncation impossible at compile time.
- Follow **Proof-Driven Development (PDD)**: whenever auditing a new feature or closing a bug, first state the adversarial threat model + prove the exact failure/extraction bound, fix the implementation, prove the `SvmState.mem` bytecode refinement, and execute the exact adversarial exploit in LiteSVM against the compiled `.so` ELF.
- Whenever modifying `lean-svm` lowering/regalloc/peephole passes, immediately run ALL verified example ELFs + downstream LiteSVM adversarial & fuzz suites.

---

### 16. Adversarial External PropAMM / Matcher CPI-Out Containment (0 Signer Delegation)

**The Bug:**
- **CPI-In signer delegation:** Having a taker call an untrusted third-party matcher which CPIs into core with `takerOwner (S)` delegates the taker's top-level signer authority to closed-source code (enabling SOL/SPL drains or spoofed trades).
- **`noop.so` / stale-buffer quote replay:** Reading a quote struct written by an external matcher without a monotonic nonce lets a no-op program replay a stale quote forever.
- **Unbounded fill / abusive pricing / self-CPI / re-entrancy:** Passing core state accounts or skipping core-side `fillQty ≤ maxQty`, `limitPrice`, `maxMoveBps`, or `matcherProg != progId` checks lets a malicious matcher over-fill, manipulate price, or re-enter core.

**How to Prevent:**
- Use **0-signer CPI-Out** from core to `matcherProg`: verify `takerOwner (S)` in core ONLY, NEVER pass `takerOwner` or core writable accounts to `matcherProg` — pass strictly `[matcherCtx (W, S=0)]` (+ optional readonly non-signer `extraAcc`, ALWAYS requiring `rawLoadU8 extraAcc == ABI.nonDupMarker` so passing a core/signer account as `extraAcc` can never cause an 8-byte dup-stub memory overread!).
- Bind `lpPfl.matcherCtx` on the LP's portfolio so the LP retains 100% EOA custody (can revoke or withdraw directly at any time) and require `matcherCtx.owner == matcherProg`, `isExecutable matcherProg`, and `matcherProg != progId`.
- Pass `reqSeq = preSeq + 1` in the CPI request (wrapping `UInt64` add satisfies `preSeq + 1 ≠ preSeq` unconditionally!) and require `magic == MAGIC_MRET ∧ status == 0 ∧ seq == reqSeq` post-CPI.
- Support unified multi-market batching (`k ∈ [1..8]` distinct markets with `dupMarker == 0xFF` & distinct `marketId` checks) in ONE CPI so market makers see all offers atomically without tx introspection, while core enforces `0 < fillQty_i ≤ maxQty_i`, taker `limitPrice_i`, `maxMoveBps`, and atomic rollback across all `k` legs.
- **Universal economic buy/sell spread direction across open & reduce:** Never key spread/limit direction on raw `takerIsLong` when closing (`mode = 1`): closing an existing Long is a **SELL** (receives Bid `≤ markP`, floored by `≥ limitPrice`), and closing an existing Short is a **BUY** (pays Ask `≥ markP`, capped by `≤ limitPrice`). Compute `takerIsBuying = (mode == 0 && takerIsLong) || (mode == 1 && !takerIsLong)` in both core limit checks and matchers, and swap `applyExecSpread` arguments on `mode = 1` so third-party PropAMMs using standard Bid/Ask quotes never invert spread payments on reduces.
- **Ceiling virtual reserves & auto-closed receipts:** In virtual-reserve batch auctions (`xy = k`), compute `virtBids = mulDiv64Ceil totalPot resRate POS_SCALE` (never floor!) so `virtBids ≥ 1` holds unconditionally even on tiny pots (`totalPot * resRate < 1e6`), discharging the quiet-epoch price-cap precondition (`B_virt > 0`). In one-shot claim handlers (`ClaimQuote`), auto-close the per-bid receipt (`zeroWords` + `MAGIC_CLOSED` + refund lamports to `bidder (W, S)` with `bidReceipt != bidder` aliasing check) to prevent permanent per-bid rent leaks with zero extra opcodes.

**LiteSVM Test Recipe:**
- Compile a real adversarial `evil_matcher.so` attacking all vectors (over-fill, abusive `limitPrice`, nonzero `status`, stale `seq` / `noop.so`, bad magic, zero fill, exceeding `maxMoveBps`, writing readonly `extraAcc`, aliased duplicate market in batch, self-CPI) and verify every attack reverts cleanly while multi-market correlated baskets succeed atomically (and LP earns spread on BOTH opens and reduces).
- Verify small-pot `virtBids == 1` (`totalPot * resRate < 1e6`) blocks 100% drain by a 1-atom bidder, and verify `ClaimQuote` refunds 100% of receipt rent lamports to `bidder` while blocking double-claim / same-tx revival.

---

## Pre-Deployment Verification Checklist

Before deploying any `lean-svm` program to devnet or mainnet:

1. **Zero `sorry`, zero custom axioms:** Run `#print axioms` on every theorem — only standard Lean axioms (`propext`, `Quot.sound`, `Classical.choice`, `Lean.ofReduceBool` / `bv_decide`).
2. **Audit every handler's account header checks:**
   - `isSigner` on all authorities
   - `isWritable` on all mutated accounts
   - `owner == progId` on all program state accounts
   - Exact `dataLen == exactSize`
   - Type magic check (`!= 0`, `!= MAGIC_CLOSED`)
   - Distinct-key checks (`!=`) for all aliasable pairs (`dest != vault`, `from != to`, `partyA != partyB`, `escrow != sink`)
   - Canonical CPI program ID pinning (`checkTokenProg` / `checkTokenOr2022Prog` / `checkSystemProg`)
   - Balance-delta accounting (`postBal - preBal`) on arbitrary external SPL/Token-2022 deposits
3. **Audit every init & close path:**
   - Full `zeroWords` on fresh init AND close
   - Permanent nonzero `MAGIC_CLOSED` tombstone on close
   - Verified with a `SvmState.mem` theorem (not just a `Nat` model!)
4. **Audit real-world Solana mainnet threat model:**
   - `K = 4` consecutive adversarial leader slots & exact compounded move envelopes
   - Cross-market / multi-account isolation (unrelated adversarial market cannot steal funds or stale-oracle DoS healthy markets)
   - Anti-MEV / anti-spam batch clearing (`O(1)` settlement, irrevocable bids, virtual-reserve quiet-epoch cap, overflow-free self-calibration)
5. **Run adversarial LiteSVM tests** covering every applicable item (#1–#15 above), plus a multi-step stateful invariant fuzzer against real SPL Token / Token-2022 / wSOL accounts (zero vault mocks).
