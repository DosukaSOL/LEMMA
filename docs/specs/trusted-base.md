# Trusted base: what LEMMA's guarantees rest on

A machine-checked proof is only as strong as its assumptions. This page lists everything a LEMMA
guarantee depends on that is **not** itself proven.

## 1. Proof checking

| Component | Trusted for | Notes |
|---|---|---|
| Lean 4 kernel (v4.36.0) | Checking every proof | The usual trust root for Lean developments. |
| Axioms `propext`, `Classical.choice`, `Quot.sound` | Standard logic | Allowed by policy. Usage is listed per theorem in [`axiom-report.md`](axiom-report.md). |

**LEMMA's own theorems use no native-evaluation axioms.** No `native_decide` or `bv_decide`, so no
`Lean.ofReduceBool` and no `*._native.*` axioms; `lake exe lemma-audit` fails the build if one
appears.

Upstream lean-svm is different: **36 of its 621 theorems** depend on `bv_decide`'s native axioms.
These trust Lean's compiler and the bundled LRAT checker as well as the kernel. Examples are
`vault_transfer_conserves_lamports`, `mulDiv64_ok_spec` and the core `SvmState` memory lemmas. The
full list is in the axiom report. **LEMMA's proofs don't use any of them.** LEMMA has its own
kernel-only `mulDiv` and key comparison for exactly this reason.

## 2. From Lean definition to running program

| Component | Trusted for | Mitigation |
|---|---|---|
| lean-svm compiler (Lean → sBPF), **with LEMMA patches 0001 and 0002** | That the `.so` behaves like the Lean definition | The compiler is **not verified end to end**. Upstream proves 60 lemmas about individual passes. LEMMA adds differential testing: every LEMMA program is compiled and its results compared with the Lean definition, or with an exact `Nat` reference, on thousands of inputs. Testing found two upstream miscompilation bugs (see `patches/`); there may be more. |
| ELF linker / encoder (`LeanSVM/SBPF/`) | The bytes match the symbolic instructions | Upstream proves `pushRawInsn_roundtrip` (it uses `bv_decide`). LEMMA's interpreter runs the *symbolic* instructions, so it doesn't check encoding. **Only the LiteSVM job in CI executes the real ELF bytes.** |
| LEMMA's sBPF interpreter (`tests/LemmaTest/Sbpf.lean`) | Test results | Ordinary unverified test code, written independently of the compiler and deliberately strict (garbage in caller-saved registers after syscalls, poisoned uninitialised stack, strict memory regions). It is a test oracle, not Agave. |

## 3. Solana runtime

| Assumption | Used by |
|---|---|
| The loader serializes the input buffer in ABI v1 layout (flags, key, owner, lamports, data, …) | Every account predicate in `Lemma.Spec.Accounts` |
| `is_signer` / `is_writable` flags are set truthfully by the runtime | `Signer`, `Writable` |
| The 32 bytes after the instruction data are the **executing program's id** | `OwnedBy … progId` in `GuardedCounter` |
| Each distinct account appears in exactly one non-duplicate slot; repeats use duplicate markers | Rejecting duplicates via `NonDup` |
| sBPF v0 semantics (wrapping 64-bit ALU, `mov32` zero-extension, `div`/`mod` by zero aborts, `abort` syscall terminates the instruction) | Patch 0001, and all compiled code |
| Rent, account ownership transfer, and lamport accounting by the runtime | Not used yet: there are no lamport- or rent-moving LEMMA programs |

## 4. Syscalls and CPIs: modelled as stubs

lean-svm's `SvmState` model gives syscalls **placeholder** semantics:
- `sysMemcmp` compares one byte;
- `sysSha256` doesn't hash;
- `sysInvokeSignedC` (CPI) always "succeeds" and has no effect on other accounts.

**Any theorem whose proof goes through a syscall or CPI says nothing about the real syscall.**
LEMMA's current theorems use none of them; the guards use plain loads. Future components that
make CPIs (for example token transfers) must treat the CPI target's behaviour as an assumption and
state it explicitly.

## 5. Not covered at all

- Canonical PDA bumps. lean-svm has no `sol_create_program_address` /
  `sol_try_find_program_address` binding, so programs can't verify a bump on-chain yet.
- Compute-unit limits and stack-depth limits on the real VM.
- Upgrade authority and deployment configuration.
- Anything the specifications don't state. A theorem constrains only what it says.
