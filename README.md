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
| **Counter** (init / inc / add) | **1,040 B** | 1,696 B | **1.63× smaller** | **24 / 29 / 31 CU** | 27 / 32 / 37 CU | 0 B |
| **Vault** (3 accs + 32B eq + `sol_log_`) | **1,976 B** | 2,304 B | **1.17× smaller** | **167 CU** | 177 CU | 0 B |
| **DutchAuction** (Token-2022 NFT + Clock + CPI) | **6,896 B** | 12,984 B | **1.88× smaller** | **3,080 / 4,579 CU** | 3,096 / 4,735 CU | 0 B |

### Full Formally Verified DeFi & NFT Protocol Suite (SPL Token + SPL Token-2022 on LiteSVM)

| Program | Instructions | `.text` | Stack | Heap | `.so` Size | LiteSVM CUs | Formal Lean 4 Proofs |
|---|---:|---:|---:|---:|---:|---|---|
| [`Examples.Noop`](Examples/Noop.lean) | 2 | 16 B | 0 B | 0 B | **352 B** | 2 | `noop_always_succeeds` |
| [`Examples.Counter`](Examples/Counter.lean) | 88 | 704 B | 0 B | 0 B | **1,040 B** | 24 / 29 / 31 | `counter_increment_adds_one`, `counter_increment_overflow_rejected` |
| [`Examples.Vault`](Examples/Vault.lean) | 119 | 952 B | 0 B | 0 B | **1,976 B** | 167 | `vault_transfer_conserves_lamports`, `vault_rejects_insufficient_funds` |
| [`Examples.HashCheck`](Examples/HashCheck.lean) | 75 | 600 B | 56 B | 0 B | **1,736 B** | 394 | `sol_sha256` + `sol_get_clock_sysvar` + `sol_log_` |
| [`Examples.Amm`](Examples/Amm.lean) (SPL + Token-2022) | 1,162 | 9,296 B | 384 B | 0 B | **10,224 B** | init 128, addLiq 4,537, swap 4,555, remLiq 4,571 | `amm_swap_preserves_k`, `amm_swap_never_drains_reserve` |
| [`Examples.Lending`](Examples/Lending.lean) (SPL + Token-2022) | 1,246 | 9,968 B | 384 B | 0 B | **11,024 B** | init 296, dep 1,642, bor 3,379, liq 4,854, rep 3,256 | `lending_repay_monotone`, `lending_healthy_cannot_be_liquidated` |
| [`Examples.DutchAuction`](Examples/DutchAuction.lean) (Token-2022 NFT) | 736 | 5,888 B | 384 B | 0 B | **6,896 B** | create 3,080, buyNow 4,579 | `dutchPrice_bounded`, `dutchPrice_monotone` |
| [`Examples.BondingCurve`](Examples/BondingCurve.lean) (Token-2022 Mint/Burn) | 829 | 6,632 B | 304 B | 0 B | **7,592 B** | init 99, buy 4,885, sell 3,625 | `curve_buy_preserves_k`, `curve_sell_bounded_by_reserve` |

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
      • Call-site-count smart auto-outlining into 1-CU sBPF `call` functions
      • Automatic stack argument-packing for `> 5`-arg outlined helpers (up to 12 scalar params)
      • Reusable per-function out-pointer & arg-pack stack slots + high-water-mark frame reuse
   │
   ▼  LeanSVM.Compiler.Optimize (fixed-point SSA pipeline)
      • Copy & constant block-parameter propagation
      • Constant folding & power-of-2 strength reduction (`mul/div/mod` → `lsh/rsh/and`)
      • Immediate operand folding (`binImm`, `storeImm` → `stdw`/`stw`/`sth`/`stb`)
      • Address-offset & direct `r10` stack load/store folding (`[r10 - off]`)
      • Compare-and-branch fusion & operand flipping (`1 <= r` → `r >= 1`)
      • Local pure-ALU CSE, load-CSE, store-to-load forwarding, and DCE
      • Constant-return AND variable-return exit-block tail-merging (eliminates hot-path error spills!)
      • Balanced O(log2 N) binary-search switch dispatch (`switchDispatchPass`)
   │
   ▼  LeanSVM.Compiler.RegAlloc
      • Loop-aware RPO block ordering + natural loop 10× use weighting
      • SSA constant rematerialization (`Loc.imm`, zero register pressure / zero spills)
      • Exact iterative backward `liveIn`/`liveOut` CFG liveness
      • Coalescing linear-scan allocator over sBPF `r0..r9` (`r6..r9` callee-saved across calls)
      • Lifetime-verified spill-slot recycling (0 stack bytes when no spills or stack buffers)
   │
   ▼  LeanSVM.Compiler.CodeGen + LeanSVM.SBPF.Peephole
      • Commutative 2-address operand swapping (1 insn instead of 3)
      • Cycle-safe parallel register/stack edge moves + zero-cost no-op edge elision
      • Basic-block register value tracking (`bbValueTrackPass` across constants & stack slots)
      • Branch-over-jump inversion, jump-to-exit forwarding, `mov+ldx` folding, `lddw` shrinking
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
- [`LeanSVM/Math.lean`](LeanSVM/Math.lean) — Overflow-safe 128-bit `mulDiv64` / `mulDiv64Ceil` (fast 64-bit path + shared 128-bit fallback) & Newton `isqrt64`
- [`LeanSVM/CPI.lean`](LeanSVM/CPI.lean) — Zero-heap stack-allocated `sol_invoke_signed_c` CPIs for **SPL Token**, **SPL Token-2022** (`TransferChecked`, `MintTo`, `Burn`, `InitializeAccount3`), PDA signing, and `SystemProgram` (`Transfer`, PDA-signed `Allocate`, PDA-signed `Assign`)
- [`LeanSVM/SBPF/`](LeanSVM/SBPF/) — Native sBPF v0/v3 ISA encoder, Murmur3-32 hasher, disassembler, peephole & value-tracking optimizer, and ELF64 `.so` linker
- [`LeanSVM/Compiler/`](LeanSVM/Compiler/) — `IR`, `Lower`, `Optimize`, `RegAlloc`, `CodeGen`, `Driver`, and **`Proofs`** (52 kernel-checked compiler soundness theorems)

---

## Formal Compiler Soundness (`LeanSVM/Compiler/Proofs.lean`)

The production compiler passes (`CodeGen`, `RegAlloc`, `Optimize`, `Peephole`, and `ISA`) are directly machine-checked against a formal small-step sBPF machine semantics in [`LeanSVM/Compiler/Proofs.lean`](LeanSVM/Compiler/Proofs.lean) (**52 theorems, 0 `sorry`, 0 custom axioms**):

- **Memory & Stack Disjointness:** `loadBytes_storeBytes_b8_same`, `loadBytes_storeBytes_b1_same`, `loadBytes_storeBytes_b8_nonOverlapping_stack` (proves non-overlapping 8-byte stack-slot invalidation in `bbValueTrackPass`).
- **ISA & Constant Materialization:** `fitsInt32_signExt32`, `fitsUInt32_zeroExt32`, `emitConst64_sound`, `JmpCond.invert_sound`, `CmpOp.toJmpCond_sound`, `CmpOp.invert_sound`, `CmpOp.flip_sound`, `BinOp.isCommutative_sound`.
- **Optimizer Soundness:** `log2IfPow2_spec`, `mul64_pow2_eq_lsh64`, `div64_pow2_eq_rsh64`, `mod64_pow2_eq_and64`, `posInt32_imm_ext_eq`, `opt_algebraic_identities`, `add64_combine_imm_sound`.
- **Peephole Rewrite Soundness:** `shrinkInsn_sound` (caught and eliminated an unsound `alu32Reg .mov d d` no-op rule), `peephole_mov_ldx_sound`, `peephole_mov_swap_drop_sound`, `peephole_stx_ldx_b8_same_sound`, `peephole_stx_ldx_b8_diff_sound`, `peephole_add64_combine_sound`.
- **CodeGen Soundness & Zero-Clobber Frame Conditions:** `loadVReg_sound`, `storeVReg_sound`, `emitSingleLocMove_sound`, **`emitStmt_cmp_sound`** (proves spill-alias safety when `dst` and `lhs` share `r0`), **`emitStmt_binOp_sound`** (all 21 64/32-bit ops across all reg/stack/imm combinations), `emitStmt_binImm_sound`, `emitStmt_constImm_sound`, `emitStmt_mov_sound`, `emitStmt_neg64_sound`, `emitStmt_load_sound`, `emitStmt_store_sound`, `emitStmt_storeImm_sound`, `emitStmt_loadStack_sound`, `emitStmt_storeStack_sound`, `emitStmt_storeStackImm_sound`, `emitStmt_stackAddr_sound`.
- **RegAlloc Scratch Safety:** `funcUsesScratchR5_complete` (proves `r5` is reserved whenever any `.binOp`, `.cmp`, `.store`, or `.brCmp` reloads a `.stack` or rematerialized `.imm` operand into `r5`).
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
