# Specifications: every LEMMA theorem in plain English

Each entry gives the Lean name, what the theorem says in plain English, and what it doesn't say.
Read the Lean statement before relying on a theorem; the English is a summary.

- **Axioms.** Every theorem below uses only Lean's standard axioms (`propext`, `Classical.choice`,
  `Quot.sound`). This is checked mechanically by `lake exe lemma-audit`; see
  [`axiom-report.md`](axiom-report.md).
- **What is trusted rather than proven:** see [`trusted-base.md`](trusted-base.md).

Notation: for a 64-bit value `x`, "`x` as an integer" means `x.toNat`, its value in `0 … 2^64 − 1`.
On-chain functions run in `SolanaM`, lean-svm's model of a program step. A step either succeeds
with a value and a new VM state (`.ok v s'`) or fails with an error code (`.err c s'`).

---

## 1. Compiler patch 0001: `Nat` lowering (`Lemma/Compiler/NatLowering.lean`)

These lemmas justify the instruction sequences that [patch 0001](../patches/0001-sound-nat-lowering.md)
emits. Each is stated over `UInt64`, whose arithmetic wraps modulo 2^64 exactly like the sBPF
`add64`/`mul64`/`sub64`/`div64`/`mod64` instructions.

| Theorem | Plain English |
|---|---|
| `add_abort_iff` | The wrapped sum `a + b` is smaller than `a` **exactly when** the true sum is ≥ 2^64. So the patch aborts on precisely the additions that overflow. |
| `add_exact` | If that check doesn't fire, the wrapped sum equals the true sum. |
| `mul_abort_iff` | For `a ≠ 0`: `(a·b mod 2^64) / a ≠ b` **exactly when** the true product is ≥ 2^64. |
| `mul_exact`, `mul_exact_of_zero` | If the check doesn't fire (or `a = 0`), the wrapped product equals the true product. |
| `sub_exact` | `if a < b then 0 else a − b` equals Lean's truncated natural subtraction. |
| `div_exact` | `if b = 0 then 0 else a / b` equals Lean's natural division (where `x / 0 = 0`). |
| `mod_exact` | `if b = 0 then a else a % b` equals Lean's natural remainder (where `x % 0 = x`). |
| `trunc32_exact` | Clamping a register value at `2^32 − 1` equals `UInt32.ofNatClamp` (formerly `ofNatTruncate`). |

**Not proven:** that `Lower.lean` actually emits these sequences, or anything about later compiler
passes. That part is covered by tests (9 probe programs, about 9,000 checks; see the patch document).

---

## 2. Math library (`Lemma/Math/`)

### 2.1 128-bit intermediate arithmetic (`Wide.lean`)

| Theorem | Plain English |
|---|---|
| `mulWide_spec` | `mulWide a b = (hi, lo)` satisfies `hi·2^64 + lo = a·b` exactly, for all 64-bit `a`, `b`. |
| `div128Loop_spec` | Invariant of the long-division loop: after processing `n` bits, the computed quotient and remainder satisfy `Q·d + R = (previous value)·2^n + (next n bits of lo)`, and `R < d`. |
| `div128Loop_eq` | The on-chain loop (which returns only the quotient) computes the same quotient as the reference loop (which also returns the remainder). |
| `div128_spec` | If `hi < d`, then `div128 hi lo d` is exactly `⌊(hi·2^64 + lo) / d⌋`, and `lo − q·d` (wrapping) is exactly the remainder. |
| `window_step`, `step_rem`, `shl1`, `shr63`, `toNat_*` | Arithmetic helper facts used by the proofs above, about shifts, masks and one division step. |

### 2.2 `mulDiv` with explicit rounding (`MulDiv.lean`)

| Theorem | Plain English |
|---|---|
| `mulDivFloor_spec` | The pure `mulDivFloor a b d` returns `some q` **if and only if** `d ≠ 0`, `⌊a·b/d⌋ < 2^64`, and `q = ⌊a·b/d⌋`. It never wraps silently, and it succeeds on **every** input whose result fits. The product `a·b` may be as large as about 2^128. |
| `mulDivCeil_spec` | The same for `⌈a·b/d⌉`. |
| `mulDivFloorM_eq`, `mulDivCeilM_eq` | The on-chain `SolanaM` versions return exactly what the pure functions return, without changing state. When the pure function returns `none`, they fail with `LErr.divByZero` (if `d = 0`) or `Err.arithmeticOverflow` (otherwise). |
| `mulDivFloorM_ok_iff`, `mulDivCeilM_ok_iff` | The on-chain versions succeed with `q` **iff** the exact rounded result is defined, fits, and equals `q`, and the state is unchanged. |
| `mulDivFloorM_bounds` | A successful floor result satisfies `q·d ≤ a·b < (q+1)·d`. |
| `mulDivCeilM_bounds` | A successful ceil result satisfies `a·b ≤ q·d < a·b + d`. |

### 2.3 Fixed point (`FixedPoint.lean`)

A value `x` at scale `S` represents `x / S`.

| Theorem | Plain English |
|---|---|
| `fpMulM_floor_bounds` | Fixed-point product rounded down: `q·S ≤ x·y < (q+1)·S`. |
| `fpMulM_ceil_bounds` | Fixed-point product rounded up: `x·y ≤ q·S < x·y + S`. |
| `fpDivM_floor_bounds` | Fixed-point quotient rounded down: `q·y ≤ x·S < (q+1)·y`. |
| `fpDivM_ceil_bounds` | Fixed-point quotient rounded up: `x·S ≤ q·y < x·S + y`. |

So a rounded result is always within one unit in the last place of the exact value, and on the
stated side.

### 2.4 Constant-product swap (`ConstantProduct.lean`)

`swapOutM x y amountIn feeBps` quotes the output of a swap into a pool with reserves `x` (input
side) and `y` (output side). All four theorems are about **this on-chain function**, not a separate
model, and they hold for every input on which it succeeds.

| Theorem | Plain English |
|---|---|
| `swapOutM_ok` | On success: the fee is ≤ 100%; the amount credited to the curve is `aif = ⌊amountIn·(10000 − fee)/10000⌋`; `x + aif` neither overflows nor is 0; and `out = ⌊y·aif / (x + aif)⌋`. The state is unchanged. |
| `swapOutM_k_nondecreasing` | **The pool's invariant can't decrease:** `(x + amountIn)·(y − out) ≥ x·y`. The fee stays in the pool. |
| `swapOutM_lt_reserve` | **The swap can't drain the pool:** `out < y` whenever `x > 0` (if `y = 0` then `out = 0`). |
| `swapOutM_rounds_for_pool` | **Rounding favours the pool:** `out·(x + aif) ≤ y·aif`, i.e. the trader never receives more than the exact real-valued quote. |
| `swapOutM_fee_rounds_for_pool` | **The fee rounds in the pool's favour:** `aif·10000 ≤ amountIn·(10000 − fee)`, and `aif ≤ amountIn`. |

**Not covered:** token transfers (CPIs), slippage limits, and pool state updates. This is a quote
function; a full AMM program would build those on top of it.

### 2.5 Non-vacuity witnesses (`Witnesses.lean`)

The theorems above have the form "if it succeeds, then …". The witnesses show by **kernel
evaluation** (`decide`, no native code) that success is possible:

| Theorem | Plain English |
|---|---|
| `mulDivFloorM_can_succeed` | `mulDivFloorM 7 6 4` succeeds with `10`. |
| `mulDivCeilM_can_succeed` | `mulDivCeilM 7 6 4` succeeds with `11`. |
| `swapOutM_can_succeed` | A 0.30%-fee swap of 1,000 into a 1,000,000 / 1,000,000 pool succeeds with `996`. |
| `fpMulM_can_succeed` | `1.5 × 2.5 = 3.75` at scale 10^9. |

The differential tests also run thousands of successful compiled executions.

---

## 3. Account validation (`Lemma/Spec/Accounts.lean`, `Lemma/Guard.lean`)

Predicates (specifications) over the serialized input buffer:

| Predicate | Meaning |
|---|---|
| `NonDup s acc` | The slot is a full account entry, not an 8-byte duplicate marker. |
| `Signer s acc` | The account signed the transaction. |
| `Writable s acc` | The account was passed writable. |
| `KeyEq s p q` | The 32-byte keys at `p` and `q` are equal. |
| `OwnedBy s acc prog` | The account's owner field equals the key at `prog`. |
| `HasKey s acc k` | The account's own key equals the key at `k`. |
| `HasTag s acc tag` | The account data is at least 8 bytes long and starts with the kind tag `tag`. |

| Theorem | Plain English |
|---|---|
| `requireNonDup_guard`, `requireSigner_guard`, `requireWritable_guard`, `requireOwner_guard`, `requireKey_guard`, `requireTag_guard` | Each runtime check **succeeds exactly when** its predicate holds, without changing state. Otherwise it fails with a fixed error code, also without changing state. |
| `keyEq_eq` | The runtime key comparison returns exactly whether `KeyEq` holds. |
| `guard_bind_ok` | If a program that starts with a check succeeds, the check's predicate held in the initial state, and the rest of the program ran from that same state. |
| `guard_bind_err` | If the predicate fails, the whole program fails with the check's code and no state change. |

Additional guard and composition lemmas (`Lemma/Guard.lean`):

| Theorem | Plain English |
|---|---|
| `requireDisjoint_guard` | The runtime check `requireDisjoint p q` succeeds **exactly when** the 8-byte fields at `p` and `q` don't overlap (`Mem.Disjoint8 p q`). |
| `bind_ok_inv`, `require_bind_ok` | Stepping lemmas: a successful sequential program is a successful first step followed by a successful rest. A successful `require c` means `c` was true. |
| `checkedAdd64_ok`, `checkedSub64_ok` | A successful checked add or subtract returns the exact integer result and doesn't change state. |

## 4. Memory model (`Lemma/Mem.lean`)

Upstream's versions of these facts are proved with `bv_decide` (native code), so LEMMA re-proves
them with the kernel alone. They are what allows theorems about the state **after** a program writes.

| Theorem | Plain English |
|---|---|
| `readU64_writeU64_same` | Reading a 64-bit word right after writing it returns the written value. |
| `readU64_writeU64_disjoint` | Writing a word doesn't change any word whose 8 bytes don't overlap it (`Disjoint8`, modulo 2^64). |
| `mem_writeU64_of_ne` | A byte outside a written word is unchanged. |
| `readU32_toNat`, `readU64_toNat` | A loaded word equals the little-endian sum of its bytes. |
| `ne_of_disjoint8`, `disjoint8_comm`, `add_eq_add_iff`, `self_eq_add_iff`, `add_eq_self_iff` | Address-arithmetic helpers. |

## 5. Parsing (`Lemma/Parse.lean`)

| Theorem | Plain English |
|---|---|
| `nextCursor_state`, `skipAccounts_state` | Walking the account list never changes the VM state. |
| `parse5_ok` | The 5-account parser doesn't change state, and the first account is at `input + 8`. |

## 6. Component: fee splitter (`Lemma/Components/FeeSplitter*.lean`)

The program splits lamports from a program-owned vault to three recipients fixed in its
configuration, by basis-point shares. **Rounding:** recipients 1 and 2 get their floor share;
recipient 0 gets the rest, i.e. its own floor share plus the dust.

| Theorem | Plain English |
|---|---|
| `split_dust_bound` | If the shares sum to 10,000 bps, recipient 0's remainder share is between its own floor share and that floor + 2. **The dust is at most 2 lamports**, and the two floor shares never exceed the amount. |
| `validBps_toNat` | The on-chain share check means the three shares really sum to 10,000; a wrapped `u64` sum can't pass. |
| `splitIx_spec` | **About the deployed `Split` handler.** Whenever it succeeds: (1) every check held: 5 non-duplicate slots, authority signed, vault and recipients writable, vault owned by the program, vault tagged, signer and recipients equal to the configured keys. (2) Exact accounting: the shares sum **exactly** to `amount`; recipient 1 and 2 get `⌊amount·bps/10000⌋`; recipient 0's share satisfies the dust bound; the vault loses exactly `amount`, which it had; each recipient gains exactly its share; the vault keeps at least its reserve; and **the total lamports of the four accounts are conserved.** |
| `initIx_spec` | **About the deployed `Init` handler.** Whenever it succeeds: every check held; the vault was **uninitialized** (tag 0) and had the right size; the configured shares sum to 10,000; the reserve was covered; and the vault is now tagged as initialized. |
| `initIx_rejects_initialized` | **Re-initialization is impossible:** `Init` never succeeds on a vault whose tag is already set. |
| `entrypoint_dispatch` | Whenever the deployed entrypoint succeeds, it ran exactly one of the two handlers, from the initial state, with the authority in the first slot. So the two `_spec` theorems cover every successful transaction. |

Non-vacuity: the hypotheses are satisfiable. The test suite runs successful `Init` and `Split`
transactions on both the compiled binary and the Lean definition, which must agree byte for byte,
and on LiteSVM.

## 7. Example program: `GuardedCounter` (`Lemma/Examples/GuardedCounter.lean`)

| Theorem | Plain English |
|---|---|
| `entrypoint_checks` | **About the deployed entrypoint:** whenever `entrypoint` succeeds, the authority slot (the first account) was a non-duplicate signer, and the counter slot was a non-duplicate, writable account, owned by the program id from the input, with the counter kind tag. |
| `parse2_ok` | Parsing the account list never changes the VM state, and the first account is at `input + 8` (built on `Lemma.Parse`). |

`entrypoint_checks` is backed by 12 attack scenarios that run on **both** the compiled binary and
the Lean definition and must agree (`tests/LemmaTest/GuardTests.lean`). That includes an honest
successful run, so the theorem's hypothesis is satisfiable.
