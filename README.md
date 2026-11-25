# `lean-svm` — Native Lean 4 → Solana sBPF Optimizing Compiler Toolchain

`lean-svm` is a **native, zero-dependency Lean 4 to Solana SVM (sBPF) compiler toolchain** that compiles formally verified Lean 4 programs **directly from Lean's monomorphic LCNF IR into minimal Solana sBPF ELF64 (`.so`) bytecode** — with **zero heap allocations**, **no C runtime**, **no LLVM**, and **no external Lean dependencies**.

Write Solana on-chain programs in Lean 4, prove critical invariants (lamport conservation, constant-product $k' \ge k$, LTV solvency, monotonic Dutch price decay, overflow rejection) directly in Lean 4's kernel with zero `sorry` and zero custom axioms, and compile the exact same definitions directly to sBPF binaries that **beat hand-rolled `#![no_std]` Rust (`rustc` + LLVM 22 `-O3`)** on both `.so` object size and Compute Units (CUs).

---

## Benchmarks (Verified on Real LiteSVM / Agave 3.1.3)

### Head-to-Head: `lean-svm` (Lean 4) vs Hand-Rolled `#![no_std]` Rust (Solana `rustc 1.95` / LLVM 22 `-O3 -C lto=fat -C strip=symbols`)

All Rust baselines are zero-dependency `#![no_std]` raw-pointer programs (leaner than Anchor and Pinocchio), compiled with Solana platform-tools `v1.58`, and executed on identical transactions in `litesvm 0.11.0`.

| Program | LeanSVM `.so` | Rust `-O3` `.so` | Size Advantage | LeanSVM CUs | Rust `-O3` CUs | Heap |
|---|---:|---:|---:|---:|---:|---:|
| **Noop** | **352 B** | 1,136 B | **3.23× smaller** | **2 CU** | 2 CU | 0 B |
| **Counter** (init / inc / add) | **1,024 B** | 1,696 B | **1.66× smaller** | **24 / 29 / 31 CU** | 27 / 32 / 37 CU | 0 B |
| **Vault** (3 accs + 32B eq + `sol_log_`) | **1,976 B** | 2,304 B | **1.17× smaller** | **167 CU** | 177 CU | 0 B |
| **DutchAuction** (Token-2022 NFT + Clock + CPI) | **6,936 B** | 12,984 B | **1.87× smaller** | **3,080 / 4,581 CU** | 3,096 / 4,735 CU | 0 B |

### Full Formally Verified DeFi & NFT Protocol Suite (SPL Token + SPL Token-2022 on LiteSVM)

| Program | Instructions | `.text` | Stack | Heap | `.so` Size | LiteSVM CUs | Formal Lean 4 Proofs |
|---|---:|---:|---:|---:|---:|---|---|
| [`Examples.Noop`](Examples/Noop.lean) | 2 | 16 B | 0 B | 0 B | **352 B** | 2 | `noop_always_succeeds` |
| [`Examples.Counter`](Examples/Counter.lean) | 86 | 688 B | 0 B | 0 B | **1,024 B** | 24 / 29 / 31 | `counter_increment_adds_one`, `counter_increment_overflow_rejected` |
| [`Examples.Vault`](Examples/Vault.lean) | 119 | 952 B | 0 B | 0 B | **1,976 B** | 167 | `vault_transfer_conserves_lamports`, `vault_rejects_insufficient_funds` |
| [`Examples.HashCheck`](Examples/HashCheck.lean) | 75 | 600 B | 56 B | 0 B | **1,736 B** | 394 | `sol_sha256` + `sol_get_clock_sysvar` + `sol_log_` |
| [`Examples.Amm`](Examples/Amm.lean) (SPL + Token-2022) | 1,198 | 9,584 B | 384 B | 0 B | **10,512 B** | init 128, addLiq 4,540, swap 4,556, remLiq 4,572 | `amm_swap_preserves_k`, `amm_swap_never_drains_reserve` |
| [`Examples.Lending`](Examples/Lending.lean) (SPL + Token-2022) | 1,281 | 10,248 B | 384 B | 0 B | **11,304 B** | init 297, dep 1,642, bor 3,381, liq 4,856, rep 3,257 | `lending_repay_monotone`, `lending_healthy_cannot_be_liquidated` |
| [`Examples.DutchAuction`](Examples/DutchAuction.lean) (Token-2022 NFT) | 741 | 5,928 B | 384 B | 0 B | **6,936 B** | create 3,080, buyNow 4,581 | `dutchPrice_bounded`, `dutchPrice_monotone` |
| [`Examples.BondingCurve`](Examples/BondingCurve.lean) (Token-2022 Mint/Burn) | 847 | 6,776 B | 304 B | 0 B | **7,736 B** | init 99, buy 5,018, sell 3,757 | `curve_buy_preserves_k`, `curve_sell_bounded_by_reserve` |

*(Note: For CPI programs, ~1,200–4,200 CUs of the transaction total come from the SPL Token / Token-2022 / System Program CPI executions themselves; LeanSVM program compute overhead is typically only ~100–400 CUs.)*

---

## Compiler Architecture

```
Lean 4 Source (.lean) + Kernel-Checked Proofs (Prop)
   │
   ▼  Lean 4 Elaborator & Kernel (erases all proofs, types, universes)
Lean 4 Monomorphic LCNF (`Lean.Compiler.LCNF.monoExt`)
   │
   ▼  LeanSVM.Compiler.Lower
      • Zero-cost erasure of `SvmState` ghost tokens, `Unit`, `Prop`
      • Scalar Replacement of Aggregates (SROA) for structs & slices
      • Unboxed `SvmStep` / `Option` / `Bool` / enums (0 heap objects)
      • Join-point continuation inlining (O(N) code size)
      • Tail-recursive functions → zero-call CFG loops
      • Call-site-count auto-outlining into 1-CU sBPF `call` functions
      • Scoped high-water-mark stack frame reuse across disjoint branches
   │
   ▼  LeanSVM.Compiler.Optimize (fixed-point SSA pipeline)
      • Copy & constant block-parameter propagation
      • Constant folding & power-of-2 strength reduction (`mul/div/mod` → `lsh/rsh/and`)
      • Immediate operand folding (`binImm`, `storeImm` → `stdw`/`stw`/`sth`/`stb`)
      • Address-offset & direct `r10` stack load/store folding (`[r10 - off]`)
      • Compare-and-branch fusion & operand flipping (`1 <= r` → `r >= 1`)
      • Local CSE, dead-code & dead-block-parameter elimination
      • Tail merging (deduplicates identical error-exit blocks)
   │
   ▼  LeanSVM.Compiler.RegAlloc
      • Loop-aware RPO block ordering (keeps loops tight, sinks cold exits)
      • Exact iterative backward `liveIn`/`liveOut` CFG liveness
      • Coalescing linear-scan allocator over sBPF `r0..r9` (`r6..r9` callee-saved across calls)
      • Lifetime-verified spill-slot recycling (0 stack bytes when no spills or stack buffers)
   │
   ▼  LeanSVM.Compiler.CodeGen + LeanSVM.SBPF.Peephole
      • Commutative 2-address operand swapping (1 insn instead of 3)
      • Cycle-safe parallel register/stack edge moves
      • Store-to-reload forwarding, `lddw` → `mov64`/`mov32` shrinking, fallthrough jumps
   │
   ▼  LeanSVM.SBPF.ELF
      • Direct ELF64 `.so` linker & serializer (supports `--sbpf v0` and `--sbpf v3`)
      • Zero-copy contiguous RO sections (`Section::Borrowed`); dynamic tables omitted when unused
```

---

## Project Layout

- [`LeanSVM/Types.lean`](LeanSVM/Types.lean) — Zero-copy `Ptr`, `AccountView`, `ByteSlice`, `Err`, and Solana ABI v1 offsets
- [`LeanSVM/Runtime.lean`](LeanSVM/Runtime.lean) — Pure functional `SvmState` verification model + `@[noinline]` hardware/syscall intrinsics + `bv_decide` memory read/write theorems
- [`LeanSVM/Input.lean`](LeanSVM/Input.lean) — Demand-driven zero-copy account cursor, inline/auto-outlined 32-byte `pubkeyEq`/`pubkeyCopy`, checked arithmetic
- [`LeanSVM/Math.lean`](LeanSVM/Math.lean) — Overflow-safe 128-bit `mulDiv64` (fast inline 64-bit path + shared outlined 128-bit fallback) & Newton `isqrt64`
- [`LeanSVM/CPI.lean`](LeanSVM/CPI.lean) — Zero-heap stack-allocated `sol_invoke_signed_c` CPIs for **SPL Token**, **SPL Token-2022** (`TransferChecked`, `MintTo`, `Burn`), PDA signing, and `SystemProgram::Transfer`
- [`LeanSVM/SBPF/`](LeanSVM/SBPF/) — Native sBPF v0/v3 ISA encoder, Murmur3-32 hasher, disassembler, peephole optimizer, and ELF64 `.so` linker
- [`LeanSVM/Compiler/`](LeanSVM/Compiler/) — `IR`, `Lower`, `Optimize`, `RegAlloc`, `CodeGen`, `Driver`
- [`Examples/`](Examples/) — 8 formally verified Solana programs (`Noop`, `Counter`, `Vault`, `HashCheck`, `Amm`, `Lending`, `DutchAuction`, `BondingCurve`)
- [`svm-runner/`](svm-runner/) — Minimal-dependency LiteSVM (`0.11.0` / Agave `3.1.3`) end-to-end test & Rust comparison benchmark runner
- [`benchmarks/`](benchmarks/) — Zero-dep `#![no_std]` hand-rolled Rust baseline programs

---

## Quick Start

```bash
# 1. Build SDK, compiler, and verify all Lean 4 formal proofs
lake build

# 2. Compile any Lean 4 entrypoint directly to a Solana sBPF .so binary
lake exe lean-svm build Examples.Amm Examples.Amm.entrypoint -o build/amm.so

# Optional flags:
#   --sbpf v0|v3   Target sBPF v0 (default, mainnet/Agave) or strict sBPF v3 (static syscalls)
#   --dump-ir      Print raw and optimized SbfIR
#   --dump-asm     Print generated sBPF assembly

# 3. Run full build + compile + LiteSVM verification & head-to-head Rust benchmarks
./scripts/build-and-test.sh
```
