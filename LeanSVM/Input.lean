/-
  LeanSVM.Input
  Zero-copy, demand-driven Solana SVM input buffer parser and AccountView accessors.
  Compiles to minimal register-only sBPF instructions with 0 heap allocations.
-/
import LeanSVM.Types
import LeanSVM.Runtime

namespace LeanSVM

/-! ### Zero-Copy AccountView Accessors -/

namespace AccountView

/-- Read whether this account signed the transaction (`[acc + 1] != 0`). -/
@[inline] def isSigner (acc : AccountView) : SolanaM Bool := do
  let b ← rawLoadU8 (acc + ABI.accIsSignerOffset)
  return b != 0

/-- Read whether this account is writable (`[acc + 2] != 0`). -/
@[inline] def isWritable (acc : AccountView) : SolanaM Bool := do
  let b ← rawLoadU8 (acc + ABI.accIsWritableOffset)
  return b != 0

/-- Read whether this account is executable (`[acc + 3] != 0`). -/
@[inline] def isExecutable (acc : AccountView) : SolanaM Bool := do
  let b ← rawLoadU8 (acc + ABI.accIsExecutableOffset)
  return b != 0

/-- Zero-copy pointer to the 32-byte account Pubkey (`acc + 8`). -/
@[inline] def keyPtr (acc : AccountView) : Ptr :=
  acc + ABI.accKeyOffset

/-- Zero-copy pointer to the 32-byte owner Pubkey (`acc + 40`). -/
@[inline] def ownerPtr (acc : AccountView) : Ptr :=
  acc + ABI.accOwnerOffset

/-- Read current lamport balance (`[acc + 72]`). -/
@[inline] def lamports (acc : AccountView) : SolanaM UInt64 :=
  rawLoadU64 (acc + ABI.accLamportsOffset)

/-- Write updated lamport balance (`[acc + 72] := val`). -/
@[inline] def setLamports (acc : AccountView) (val : UInt64) : SolanaM Unit :=
  rawStoreU64 (acc + ABI.accLamportsOffset) val

/-- Read account data byte length (`[acc + 80]`). -/
@[inline] def dataLen (acc : AccountView) : SolanaM UInt64 :=
  rawLoadU64 (acc + ABI.accDataLenOffset)

/-- Zero-copy pointer to account data bytes (`acc + 88`). -/
@[inline] def dataPtr (acc : AccountView) : Ptr :=
  acc + ABI.accDataOffset

/-- Zero-copy read of a `UInt8` at `off` inside account data (folds to single `ldxb [acc + 88 + off]`). -/
@[inline] def readDataU8 (acc : AccountView) (off : UInt64) : SolanaM UInt8 :=
  rawLoadU8 (acc + (ABI.accDataOffset + off))

/-- Zero-copy read of a `UInt32` at `off` inside account data (folds to single `ldxw [acc + 88 + off]`). -/
@[inline] def readDataU32 (acc : AccountView) (off : UInt64) : SolanaM UInt32 :=
  rawLoadU32 (acc + (ABI.accDataOffset + off))

/-- Zero-copy read of a `UInt64` at `off` inside account data (folds to single `ldxdw [acc + 88 + off]`). -/
@[inline] def readDataU64 (acc : AccountView) (off : UInt64) : SolanaM UInt64 :=
  rawLoadU64 (acc + (ABI.accDataOffset + off))

/-- Zero-copy write of a `UInt8` at `off` inside account data (folds to single `stxb [acc + 88 + off], v`). -/
@[inline] def writeDataU8 (acc : AccountView) (off : UInt64) (v : UInt8) : SolanaM Unit :=
  rawStoreU8 (acc + (ABI.accDataOffset + off)) v

/-- Zero-copy write of a `UInt32` at `off` inside account data (folds to single `stxw [acc + 88 + off], v`). -/
@[inline] def writeDataU32 (acc : AccountView) (off : UInt64) (v : UInt32) : SolanaM Unit :=
  rawStoreU32 (acc + (ABI.accDataOffset + off)) v

/-- Zero-copy write of a `UInt64` at `off` inside account data (folds to single `stxdw [acc + 88 + off], v`). -/
@[inline] def writeDataU64 (acc : AccountView) (off : UInt64) (v : UInt64) : SolanaM Unit :=
  rawStoreU64 (acc + (ABI.accDataOffset + off)) v

/-- Advance cursor past this account to the next account (or `ix_data_len` after the last account).
    Handles both duplicate (`dup != 0xFF`, 8-byte stride) and non-duplicate accounts
    (`((data_len + 10343) & ~7)` stride). Outlined once per binary for minimal `.so` size! -/
@[noinline] def nextCursor (acc : AccountView) : SolanaM Ptr := do
  let dup ← rawLoadU8 acc
  if dup == ABI.nonDupMarker then
    let dlen ← rawLoadU64 (acc + ABI.accDataLenOffset)
    let stride := (dlen + ABI.accStrideRoundAdd) &&& ABI.align8Mask
    return acc + stride
  else
    return acc + 8

/-- Enforce that `acc` is a full non-duplicate Solana account entry (`[acc + 0] == 0xFF`),
    preventing 8-byte duplicate-stub header overreads. -/
@[inline] def requireNonDup (acc : AccountView) (err : UInt64 := Err.invalidAccountData) : SolanaM Unit := do
  SolanaM.require ((← rawLoadU8 acc) == ABI.nonDupMarker) err

/-- Resolve an account slot that may legitimately alias an earlier non-duplicate account `prevAcc`
    at account index `prevIdx`: returns `acc` if `[acc + 0] == 0xFF`, returns `prevAcc` if
    `[acc + 0] == prevIdx`, and rejects every other duplicate index cleanly! -/
@[inline] def resolveDup (acc : AccountView) (prevIdx : UInt8) (prevAcc : AccountView)
    (err : UInt64 := Err.invalidAccountData) : SolanaM AccountView := do
  let d ← rawLoadU8 acc
  if d == ABI.nonDupMarker then return acc
  SolanaM.require (d == prevIdx) err
  return prevAcc

end AccountView

/-! ### Inline 32-Byte Pubkey Equality & Copy (Zero Syscall, Unrolled 4x u64) -/

/-- Compare two 32-byte Pubkeys at `p1` and `p2` using 4 unrolled `u64` loads.
    Avoids syscall overhead (~100 CUs) and runs in ~12 instructions (~12 CUs). Outlined once per binary. -/
@[noinline] def pubkeyEq (p1 p2 : Ptr) : SolanaM Bool := do
  let a0 ← rawLoadU64 p1
  let b0 ← rawLoadU64 p2
  if a0 != b0 then return false
  let a1 ← rawLoadU64 (p1 + 8)
  let b1 ← rawLoadU64 (p2 + 8)
  if a1 != b1 then return false
  let a2 ← rawLoadU64 (p1 + 16)
  let b2 ← rawLoadU64 (p2 + 16)
  if a2 != b2 then return false
  let a3 ← rawLoadU64 (p1 + 24)
  let b3 ← rawLoadU64 (p2 + 24)
  return a3 == b3

/-- Copy 32-byte Pubkey from `src` to `dst` using 4 unrolled `u64` loads & stores (8 instructions). -/
@[noinline] def pubkeyCopy (dst src : Ptr) : SolanaM Unit := do
  let w0 ← rawLoadU64 src
  rawStoreU64 dst w0
  let w1 ← rawLoadU64 (src + 8)
  rawStoreU64 (dst + 8) w1
  let w2 ← rawLoadU64 (src + 16)
  rawStoreU64 (dst + 16) w2
  let w3 ← rawLoadU64 (src + 24)
  rawStoreU64 (dst + 24) w3

/-! ### Zero-Copy SVM Input Buffer Navigation -/

namespace Input

/-- Number of accounts serialized in the SVM input buffer (`[input + 0]`). -/
@[inline] def numAccounts (input : Ptr) : SolanaM UInt64 :=
  rawLoadU64 input

/-- Pointer to the first account slot (`input + 8`). -/
@[inline] def firstAccount (input : Ptr) : AccountView :=
  input + 8

/-- Skip `remaining` accounts starting at `cursor`, returning the pointer to the
    instruction data length field (or next account). Compiles to a tight zero-stack sBPF loop. -/
def skipAccounts (cursor : Ptr) (remaining : UInt64) : SolanaM Ptr := do
  if h : remaining = 0 then
    return cursor
  else
    let next ← AccountView.nextCursor cursor
    skipAccounts next (remaining - 1)
termination_by remaining.toNat
decreasing_by
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hpos : 0 < remaining.toNat := by
    have hne : remaining.toNat ≠ 0 := fun hz => h (UInt64.toNat_inj.mp (by rw [hz]; rfl))
    omega
  change (remaining - 1).toNat < remaining.toNat
  rw [UInt64.toNat_sub_of_le, h1]
  · omega
  · exact UInt64.le_iff_toNat_le.mpr (by rw [h1]; omega)

/-- Given the cursor right after all accounts, return `(ixDataPtr, ixDataLen)`. -/
@[inline] def instructionDataAt (afterAccounts : Ptr) : SolanaM ByteSlice := do
  let len ← rawLoadU64 afterAccounts
  return { ptr := afterAccounts + 8, len := len }

/-- Given the cursor right after all accounts, return pointer to the 32-byte `program_id`. -/
@[inline] def programIdAt (afterAccounts : Ptr) : SolanaM Ptr := do
  let len ← rawLoadU64 afterAccounts
  return afterAccounts + 8 + len

/-- Fast-path parser for 0-account programs: returns `(ixData, programIdPtr)`. -/
@[inline] def parse0 (input : Ptr) : SolanaM (ByteSlice × Ptr) := do
  let n ← numAccounts input
  let after ← skipAccounts (firstAccount input) n
  let ixLen ← rawLoadU64 after
  let ixPtr := after + 8
  return ({ ptr := ixPtr, len := ixLen }, ixPtr + ixLen)

/-- Fast-path parser for 1-account programs: returns `(acc0, ixData, programIdPtr)`.
    Requires `num_accounts >= 1`; skips any trailing accounts beyond `acc0`. -/
@[inline] def parse1 (input : Ptr) : SolanaM (AccountView × ByteSlice × Ptr) := do
  let n ← numAccounts input
  SolanaM.require (n >= 1) Err.notEnoughAccountKeys
  let acc0 := firstAccount input
  let after0 ← AccountView.nextCursor acc0
  let after ← skipAccounts after0 (n - 1)
  let ixLen ← rawLoadU64 after
  let ixPtr := after + 8
  return (acc0, { ptr := ixPtr, len := ixLen }, ixPtr + ixLen)

/-- Fast-path parser for 2-account programs: returns `(acc0, acc1, ixData, programIdPtr)`. -/
@[inline] def parse2 (input : Ptr) : SolanaM (AccountView × AccountView × ByteSlice × Ptr) := do
  let n ← numAccounts input
  SolanaM.require (n >= 2) Err.notEnoughAccountKeys
  let acc0 := firstAccount input
  let acc1 ← AccountView.nextCursor acc0
  let after1 ← AccountView.nextCursor acc1
  let after ← skipAccounts after1 (n - 2)
  let ixLen ← rawLoadU64 after
  let ixPtr := after + 8
  return (acc0, acc1, { ptr := ixPtr, len := ixLen }, ixPtr + ixLen)

/-- Fast-path parser for 3-account programs: returns `(acc0, acc1, acc2, ixData, programIdPtr)`. -/
@[inline] def parse3 (input : Ptr) : SolanaM (AccountView × AccountView × AccountView × ByteSlice × Ptr) := do
  let n ← numAccounts input
  SolanaM.require (n >= 3) Err.notEnoughAccountKeys
  let acc0 := firstAccount input
  let acc1 ← AccountView.nextCursor acc0
  let acc2 ← AccountView.nextCursor acc1
  let after2 ← AccountView.nextCursor acc2
  let after ← skipAccounts after2 (n - 3)
  let ixLen ← rawLoadU64 after
  let ixPtr := after + 8
  return (acc0, acc1, acc2, { ptr := ixPtr, len := ixLen }, ixPtr + ixLen)

/-- Fast-path parser for 4-account programs. -/
@[inline] def parse4 (input : Ptr) :
    SolanaM (AccountView × AccountView × AccountView × AccountView × ByteSlice × Ptr) := do
  let n ← numAccounts input
  SolanaM.require (n >= 4) Err.notEnoughAccountKeys
  let a0 := firstAccount input
  let a1 ← AccountView.nextCursor a0
  let a2 ← AccountView.nextCursor a1
  let a3 ← AccountView.nextCursor a2
  let after3 ← AccountView.nextCursor a3
  let after ← skipAccounts after3 (n - 4)
  let ixLen ← rawLoadU64 after
  let ixPtr := after + 8
  return (a0, a1, a2, a3, { ptr := ixPtr, len := ixLen }, ixPtr + ixLen)

/-- Fast-path parser for 5-account programs. -/
@[inline] def parse5 (input : Ptr) :
    SolanaM (AccountView × AccountView × AccountView × AccountView × AccountView × ByteSlice × Ptr) := do
  let n ← numAccounts input
  SolanaM.require (n >= 5) Err.notEnoughAccountKeys
  let a0 := firstAccount input
  let a1 ← AccountView.nextCursor a0
  let a2 ← AccountView.nextCursor a1
  let a3 ← AccountView.nextCursor a2
  let a4 ← AccountView.nextCursor a3
  let after4 ← AccountView.nextCursor a4
  let after ← skipAccounts after4 (n - 5)
  let ixLen ← rawLoadU64 after
  let ixPtr := after + 8
  return (a0, a1, a2, a3, a4, { ptr := ixPtr, len := ixLen }, ixPtr + ixLen)

/-- Fast-path parser for 6-account programs. -/
@[inline] def parse6 (input : Ptr) :
    SolanaM (AccountView × AccountView × AccountView × AccountView × AccountView × AccountView × ByteSlice × Ptr) := do
  let n ← numAccounts input
  SolanaM.require (n >= 6) Err.notEnoughAccountKeys
  let a0 := firstAccount input
  let a1 ← AccountView.nextCursor a0
  let a2 ← AccountView.nextCursor a1
  let a3 ← AccountView.nextCursor a2
  let a4 ← AccountView.nextCursor a3
  let a5 ← AccountView.nextCursor a4
  let after5 ← AccountView.nextCursor a5
  let after ← skipAccounts after5 (n - 6)
  let ixLen ← rawLoadU64 after
  let ixPtr := after + 8
  return (a0, a1, a2, a3, a4, a5, { ptr := ixPtr, len := ixLen }, ixPtr + ixLen)

/-- Fast-path parser for 7-account programs. -/
@[inline] def parse7 (input : Ptr) :
    SolanaM (AccountView × AccountView × AccountView × AccountView × AccountView × AccountView × AccountView × ByteSlice × Ptr) := do
  let n ← numAccounts input
  SolanaM.require (n >= 7) Err.notEnoughAccountKeys
  let a0 := firstAccount input
  let a1 ← AccountView.nextCursor a0
  let a2 ← AccountView.nextCursor a1
  let a3 ← AccountView.nextCursor a2
  let a4 ← AccountView.nextCursor a3
  let a5 ← AccountView.nextCursor a4
  let a6 ← AccountView.nextCursor a5
  let after6 ← AccountView.nextCursor a6
  let after ← skipAccounts after6 (n - 7)
  let ixLen ← rawLoadU64 after
  let ixPtr := after + 8
  return (a0, a1, a2, a3, a4, a5, a6, { ptr := ixPtr, len := ixLen }, ixPtr + ixLen)

/-- Fast-path parser for 8-account programs. -/
@[inline] def parse8 (input : Ptr) :
    SolanaM (AccountView × AccountView × AccountView × AccountView × AccountView × AccountView × AccountView × AccountView × ByteSlice × Ptr) := do
  let n ← numAccounts input
  SolanaM.require (n >= 8) Err.notEnoughAccountKeys
  let a0 := firstAccount input
  let a1 ← AccountView.nextCursor a0
  let a2 ← AccountView.nextCursor a1
  let a3 ← AccountView.nextCursor a2
  let a4 ← AccountView.nextCursor a3
  let a5 ← AccountView.nextCursor a4
  let a6 ← AccountView.nextCursor a5
  let a7 ← AccountView.nextCursor a6
  let after7 ← AccountView.nextCursor a7
  let after ← skipAccounts after7 (n - 8)
  let ixLen ← rawLoadU64 after
  let ixPtr := after + 8
  return (a0, a1, a2, a3, a4, a5, a6, a7, { ptr := ixPtr, len := ixLen }, ixPtr + ixLen)

/-- Fast-path parser for 9-account programs (e.g. Multi-SPL / Token-2022 AMM Swap with dual token programs!). -/
@[inline] def parse9 (input : Ptr) :
    SolanaM (AccountView × AccountView × AccountView × AccountView × AccountView × AccountView × AccountView × AccountView × AccountView × ByteSlice × Ptr) := do
  let n ← numAccounts input
  SolanaM.require (n >= 9) Err.notEnoughAccountKeys
  let a0 := firstAccount input
  let a1 ← AccountView.nextCursor a0
  let a2 ← AccountView.nextCursor a1
  let a3 ← AccountView.nextCursor a2
  let a4 ← AccountView.nextCursor a3
  let a5 ← AccountView.nextCursor a4
  let a6 ← AccountView.nextCursor a5
  let a7 ← AccountView.nextCursor a6
  let a8 ← AccountView.nextCursor a7
  let after8 ← AccountView.nextCursor a8
  let after ← skipAccounts after8 (n - 9)
  let ixLen ← rawLoadU64 after
  let ixPtr := after + 8
  return (a0, a1, a2, a3, a4, a5, a6, a7, a8, { ptr := ixPtr, len := ixLen }, ixPtr + ixLen)

/-- Zero-overhead account-skip helper for programs that only need the first `K` accounts
    and then read `ixData` dynamically without parsing all accounts up front! -/
@[inline] def parseIxOnly (input : Ptr) : SolanaM (UInt64 × AccountView × ByteSlice × Ptr) := do
  let n ← numAccounts input
  let a0 := firstAccount input
  let after ← skipAccounts a0 n
  let ixLen ← rawLoadU64 after
  let ixPtr := after + 8
  return (n, a0, { ptr := ixPtr, len := ixLen }, ixPtr + ixLen)

/-- Strict non-duplicate parsers (`parseStrict1..parseStrict8`): enforce `[a_i + 0] == 0xFF` on
    EVERY returned account `a_0..a_{k-1}`, eliminating 8-byte duplicate-stub header overreads! -/
@[inline] def parseStrict1 (input : Ptr) (dupErr : UInt64 := Err.invalidAccountData) :
    SolanaM (AccountView × ByteSlice × Ptr) := do
  let (a0, ix, pid) ← parse1 input
  AccountView.requireNonDup a0 dupErr
  return (a0, ix, pid)

@[inline] def parseStrict2 (input : Ptr) (dupErr : UInt64 := Err.invalidAccountData) :
    SolanaM (AccountView × AccountView × ByteSlice × Ptr) := do
  let (a0, a1, ix, pid) ← parse2 input
  AccountView.requireNonDup a0 dupErr; AccountView.requireNonDup a1 dupErr
  return (a0, a1, ix, pid)

@[inline] def parseStrict3 (input : Ptr) (dupErr : UInt64 := Err.invalidAccountData) :
    SolanaM (AccountView × AccountView × AccountView × ByteSlice × Ptr) := do
  let (a0, a1, a2, ix, pid) ← parse3 input
  AccountView.requireNonDup a0 dupErr; AccountView.requireNonDup a1 dupErr
  AccountView.requireNonDup a2 dupErr
  return (a0, a1, a2, ix, pid)

@[inline] def parseStrict4 (input : Ptr) (dupErr : UInt64 := Err.invalidAccountData) :
    SolanaM (AccountView × AccountView × AccountView × AccountView × ByteSlice × Ptr) := do
  let (a0, a1, a2, a3, ix, pid) ← parse4 input
  AccountView.requireNonDup a0 dupErr; AccountView.requireNonDup a1 dupErr
  AccountView.requireNonDup a2 dupErr; AccountView.requireNonDup a3 dupErr
  return (a0, a1, a2, a3, ix, pid)

@[inline] def parseStrict5 (input : Ptr) (dupErr : UInt64 := Err.invalidAccountData) :
    SolanaM (AccountView × AccountView × AccountView × AccountView × AccountView × ByteSlice × Ptr) := do
  let (a0, a1, a2, a3, a4, ix, pid) ← parse5 input
  AccountView.requireNonDup a0 dupErr; AccountView.requireNonDup a1 dupErr
  AccountView.requireNonDup a2 dupErr; AccountView.requireNonDup a3 dupErr
  AccountView.requireNonDup a4 dupErr
  return (a0, a1, a2, a3, a4, ix, pid)

@[inline] def parseStrict6 (input : Ptr) (dupErr : UInt64 := Err.invalidAccountData) :
    SolanaM (AccountView × AccountView × AccountView × AccountView × AccountView × AccountView × ByteSlice × Ptr) := do
  let (a0, a1, a2, a3, a4, a5, ix, pid) ← parse6 input
  AccountView.requireNonDup a0 dupErr; AccountView.requireNonDup a1 dupErr
  AccountView.requireNonDup a2 dupErr; AccountView.requireNonDup a3 dupErr
  AccountView.requireNonDup a4 dupErr; AccountView.requireNonDup a5 dupErr
  return (a0, a1, a2, a3, a4, a5, ix, pid)

@[inline] def parseStrict7 (input : Ptr) (dupErr : UInt64 := Err.invalidAccountData) :
    SolanaM (AccountView × AccountView × AccountView × AccountView × AccountView × AccountView × AccountView × ByteSlice × Ptr) := do
  let (a0, a1, a2, a3, a4, a5, a6, ix, pid) ← parse7 input
  AccountView.requireNonDup a0 dupErr; AccountView.requireNonDup a1 dupErr
  AccountView.requireNonDup a2 dupErr; AccountView.requireNonDup a3 dupErr
  AccountView.requireNonDup a4 dupErr; AccountView.requireNonDup a5 dupErr
  AccountView.requireNonDup a6 dupErr
  return (a0, a1, a2, a3, a4, a5, a6, ix, pid)

@[inline] def parseStrict8 (input : Ptr) (dupErr : UInt64 := Err.invalidAccountData) :
    SolanaM (AccountView × AccountView × AccountView × AccountView × AccountView × AccountView × AccountView × AccountView × ByteSlice × Ptr) := do
  let (a0, a1, a2, a3, a4, a5, a6, a7, ix, pid) ← parse8 input
  AccountView.requireNonDup a0 dupErr; AccountView.requireNonDup a1 dupErr
  AccountView.requireNonDup a2 dupErr; AccountView.requireNonDup a3 dupErr
  AccountView.requireNonDup a4 dupErr; AccountView.requireNonDup a5 dupErr
  AccountView.requireNonDup a6 dupErr; AccountView.requireNonDup a7 dupErr
  return (a0, a1, a2, a3, a4, a5, a6, a7, ix, pid)

end Input

/-! ### Formal Agave ABI Parser Soundness Theorems (`SvmState.mem`) -/

theorem AccountView.requireNonDup_ok_iff (acc : AccountView) (err : UInt64) (s s' : SvmState) :
    AccountView.requireNonDup acc err s = .ok () s' ↔
      s.mem acc = ABI.nonDupMarker ∧ s' = s := by
  unfold AccountView.requireNonDup rawLoadU8 SolanaM.require
  dsimp only [Bind.bind, SolanaM.bind, Pure.pure, SolanaM.pure, SolanaM.fail, SvmState.readU8]
  by_cases h : s.mem acc = ABI.nonDupMarker
  · simp [h, SolanaM.pure, eq_comm]
  · simp [h, SolanaM.fail]

theorem AccountView.resolveDup_ok_iff (acc : AccountView) (prevIdx : UInt8) (prevAcc : AccountView)
    (err : UInt64) (s s' : SvmState) (res : AccountView) :
    AccountView.resolveDup acc prevIdx prevAcc err s = .ok res s' ↔
      s' = s ∧ ((s.mem acc = ABI.nonDupMarker ∧ res = acc) ∨
                (s.mem acc ≠ ABI.nonDupMarker ∧ s.mem acc = prevIdx ∧ res = prevAcc)) := by
  unfold AccountView.resolveDup rawLoadU8 SolanaM.require
  dsimp only [Bind.bind, SolanaM.bind, Pure.pure, SolanaM.pure, SolanaM.fail, SvmState.readU8]
  by_cases h1 : s.mem acc = ABI.nonDupMarker
  · simp only [h1, beq_self_eq_true, ↓reduceIte, SolanaM.pure, SvmStep.ok.injEq, true_and]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, Or.inl rfl⟩
    · rintro ⟨rfl, rfl | ⟨hne, _, _⟩⟩
      · exact ⟨rfl, rfl⟩
      · exact absurd rfl hne
  · have h1b : (s.mem acc == ABI.nonDupMarker) = false := beq_false_of_ne h1
    simp only [h1b, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : s.mem acc = prevIdx
    · have h2b : (s.mem acc == prevIdx) = true := beq_iff_eq.mpr h2
      simp only [h2b, ↓reduceIte, SolanaM.bind, SolanaM.pure, SvmStep.ok.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨rfl, Or.inr ⟨h1, h2, rfl⟩⟩
      · rintro ⟨rfl, ⟨heq, _⟩ | ⟨_, _, rfl⟩⟩
        · exact absurd heq h1
        · exact ⟨rfl, rfl⟩
    · have h2b : (s.mem acc == prevIdx) = false := beq_false_of_ne h2
      simp [h1, h2, h2b, SolanaM.bind, SolanaM.fail]

/-- Soundness of `resolveDup`: if `prevAcc` is already verified non-duplicate, the resolved
    `AccountView` is ALWAYS non-duplicate (`s.mem res = ABI.nonDupMarker`, zero dup-stub risk!). -/
theorem AccountView.resolveDup_preserves_nonDup (acc : AccountView) (prevIdx : UInt8)
    (prevAcc : AccountView) (err : UInt64) (s s' : SvmState) (res : AccountView)
    (hPrev : s.mem prevAcc = ABI.nonDupMarker)
    (h : AccountView.resolveDup acc prevIdx prevAcc err s = .ok res s') :
    s' = s ∧ s.mem res = ABI.nonDupMarker := by
  have ⟨hs, hcase⟩ := (AccountView.resolveDup_ok_iff acc prevIdx prevAcc err s s' res).mp h
  refine ⟨hs, ?_⟩
  rcases hcase with ⟨h1, rfl⟩ | ⟨_, _, rfl⟩
  · exact h1
  · exact hPrev

/-- Exact Agave ABI stride specification of `AccountView.nextCursor`:
    never mutates state (`s' = s`), advances by `8` on a duplicate stub, and advances by
    `((dataLen + 10343) &&& ~7)` on a full non-duplicate account. -/
theorem AccountView.nextCursor_exact (acc : AccountView) (s : SvmState) :
    AccountView.nextCursor acc s =
      .ok (if s.mem acc = ABI.nonDupMarker then
             acc + ((s.readU64 (acc + ABI.accDataLenOffset) + ABI.accStrideRoundAdd) &&& ABI.align8Mask)
           else acc + 8) s := by
  unfold AccountView.nextCursor rawLoadU8 rawLoadU64
  dsimp only [Bind.bind, SolanaM.bind, Pure.pure, SolanaM.pure, SvmState.readU8]
  by_cases h : s.mem acc = ABI.nonDupMarker
  · simp [h, SolanaM.bind, SolanaM.pure]
  · simp [h, SolanaM.pure]

theorem Input.skipAccounts_preserves_state (cursor : Ptr) (rem : UInt64) (s s' : SvmState) (p : Ptr)
    (h : Input.skipAccounts cursor rem s = .ok p s') : s' = s := by
  suffices ∀ (n : Nat) (c : Ptr) (r : UInt64), r.toNat = n →
      Input.skipAccounts c r s = .ok p s' → s' = s from this rem.toNat cursor rem rfl h
  intro n
  induction n with
  | zero =>
    intro c r hr hs
    have hr0 : r = 0 := UInt64.toNat_inj.mp hr
    subst hr0
    unfold Input.skipAccounts at hs
    simp [Pure.pure, SolanaM.pure] at hs
    exact hs.2.symm
  | succ k ih =>
    intro c r hr hs
    have hne : r ≠ 0 := fun h0 => by subst h0; cases hr
    rw [Input.skipAccounts] at hs
    simp only [hne, ↓reduceDIte, Bind.bind, SolanaM.bind] at hs
    rw [AccountView.nextCursor_exact] at hs
    dsimp only at hs
    have hsub : (r - 1).toNat = k := by
      have h1 : (1 : UInt64).toNat = 1 := rfl
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [h1]; omega)), h1]; omega
    exact ih _ (r - 1) hsub hs

private theorem step_requireNonDup {β : Type} {acc : AccountView} {err : UInt64}
    {f : Unit → SolanaM β} {s s' : SvmState} {b : β}
    (h : (AccountView.requireNonDup acc err >>= f) s = .ok b s') :
    s.mem acc = ABI.nonDupMarker ∧ f () s = .ok b s' := by
  cases hd : AccountView.requireNonDup acc err s with
  | err _ _ => simp [Bind.bind, SolanaM.bind, hd] at h
  | ok _ s1 =>
    have ⟨hm, hs1⟩ := (AccountView.requireNonDup_ok_iff acc err s s1).mp hd
    subst hs1
    exact ⟨hm, by simpa [Bind.bind, SolanaM.bind, hd] using h⟩

private theorem step_parse_ok {α β : Type} {m : SolanaM α} {f : α → SolanaM β}
    {s s' : SvmState} {b : β}
    (h : (m >>= f) s = .ok b s') :
    ∃ a s1, m s = .ok a s1 ∧ f a s1 = .ok b s' := by
  cases hm : m s with
  | err _ _ => simp [Bind.bind, SolanaM.bind, hm] at h
  | ok a s1 => exact ⟨a, s1, rfl, by simpa [Bind.bind, SolanaM.bind, hm] using h⟩

private theorem parse1_preserves (input : Ptr) (s s' : SvmState) (r : AccountView × ByteSlice × Ptr)
    (h : Input.parse1 input s = .ok r s') : s' = s ∧ s.readU64 input ≥ 1 := by
  unfold Input.parse1 Input.numAccounts rawLoadU64 SolanaM.require at h
  dsimp only [Bind.bind, SolanaM.bind, Pure.pure, SolanaM.pure, SolanaM.fail] at h
  by_cases hn : s.readU64 input ≥ 1
  · simp only [hn, decide_true, ↓reduceIte, SolanaM.pure, AccountView.nextCursor_exact] at h
    cases hsk : Input.skipAccounts _ _ s with
    | err _ _ => rw [hsk] at h; cases h
    | ok _ s1 =>
      rw [hsk] at h; cases h
      exact ⟨Input.skipAccounts_preserves_state _ _ _ _ _ hsk, hn⟩
  · simp [hn, SolanaM.fail] at h

private theorem parse2_preserves (input : Ptr) (s s' : SvmState)
    (r : AccountView × AccountView × ByteSlice × Ptr)
    (h : Input.parse2 input s = .ok r s') : s' = s ∧ s.readU64 input ≥ 2 := by
  unfold Input.parse2 Input.numAccounts rawLoadU64 SolanaM.require at h
  dsimp only [Bind.bind, SolanaM.bind, Pure.pure, SolanaM.pure, SolanaM.fail] at h
  by_cases hn : s.readU64 input ≥ 2
  · simp only [hn, decide_true, ↓reduceIte, SolanaM.pure, AccountView.nextCursor_exact] at h
    cases hsk : Input.skipAccounts _ _ s with
    | err _ _ => rw [hsk] at h; cases h
    | ok _ s1 =>
      rw [hsk] at h; cases h
      exact ⟨Input.skipAccounts_preserves_state _ _ _ _ _ hsk, hn⟩
  · simp [hn, SolanaM.fail] at h

private theorem parse3_preserves (input : Ptr) (s s' : SvmState)
    (r : AccountView × AccountView × AccountView × ByteSlice × Ptr)
    (h : Input.parse3 input s = .ok r s') : s' = s ∧ s.readU64 input ≥ 3 := by
  unfold Input.parse3 Input.numAccounts rawLoadU64 SolanaM.require at h
  dsimp only [Bind.bind, SolanaM.bind, Pure.pure, SolanaM.pure, SolanaM.fail] at h
  by_cases hn : s.readU64 input ≥ 3
  · simp only [hn, decide_true, ↓reduceIte, SolanaM.pure, AccountView.nextCursor_exact] at h
    cases hsk : Input.skipAccounts _ _ s with
    | err _ _ => rw [hsk] at h; cases h
    | ok _ s1 =>
      rw [hsk] at h; cases h
      exact ⟨Input.skipAccounts_preserves_state _ _ _ _ _ hsk, hn⟩
  · simp [hn, SolanaM.fail] at h

private theorem parse4_preserves (input : Ptr) (s s' : SvmState)
    (r : AccountView × AccountView × AccountView × AccountView × ByteSlice × Ptr)
    (h : Input.parse4 input s = .ok r s') : s' = s ∧ s.readU64 input ≥ 4 := by
  unfold Input.parse4 Input.numAccounts rawLoadU64 SolanaM.require at h
  dsimp only [Bind.bind, SolanaM.bind, Pure.pure, SolanaM.pure, SolanaM.fail] at h
  by_cases hn : s.readU64 input ≥ 4
  · simp only [hn, decide_true, ↓reduceIte, SolanaM.pure, AccountView.nextCursor_exact] at h
    cases hsk : Input.skipAccounts _ _ s with
    | err _ _ => rw [hsk] at h; cases h
    | ok _ s1 =>
      rw [hsk] at h; cases h
      exact ⟨Input.skipAccounts_preserves_state _ _ _ _ _ hsk, hn⟩
  · simp [hn, SolanaM.fail] at h

private theorem parse5_preserves (input : Ptr) (s s' : SvmState)
    (r : AccountView × AccountView × AccountView × AccountView × AccountView × ByteSlice × Ptr)
    (h : Input.parse5 input s = .ok r s') : s' = s ∧ s.readU64 input ≥ 5 := by
  unfold Input.parse5 Input.numAccounts rawLoadU64 SolanaM.require at h
  dsimp only [Bind.bind, SolanaM.bind, Pure.pure, SolanaM.pure, SolanaM.fail] at h
  by_cases hn : s.readU64 input ≥ 5
  · simp only [hn, decide_true, ↓reduceIte, SolanaM.pure, AccountView.nextCursor_exact] at h
    cases hsk : Input.skipAccounts _ _ s with
    | err _ _ => rw [hsk] at h; cases h
    | ok _ s1 =>
      rw [hsk] at h; cases h
      exact ⟨Input.skipAccounts_preserves_state _ _ _ _ _ hsk, hn⟩
  · simp [hn, SolanaM.fail] at h

private theorem parse6_preserves (input : Ptr) (s s' : SvmState)
    (r : AccountView × AccountView × AccountView × AccountView × AccountView × AccountView × ByteSlice × Ptr)
    (h : Input.parse6 input s = .ok r s') : s' = s ∧ s.readU64 input ≥ 6 := by
  unfold Input.parse6 Input.numAccounts rawLoadU64 SolanaM.require at h
  dsimp only [Bind.bind, SolanaM.bind, Pure.pure, SolanaM.pure, SolanaM.fail] at h
  by_cases hn : s.readU64 input ≥ 6
  · simp only [hn, decide_true, ↓reduceIte, SolanaM.pure, AccountView.nextCursor_exact] at h
    cases hsk : Input.skipAccounts _ _ s with
    | err _ _ => rw [hsk] at h; cases h
    | ok _ s1 =>
      rw [hsk] at h; cases h
      exact ⟨Input.skipAccounts_preserves_state _ _ _ _ _ hsk, hn⟩
  · simp [hn, SolanaM.fail] at h

private theorem parse7_preserves (input : Ptr) (s s' : SvmState)
    (r : AccountView × AccountView × AccountView × AccountView × AccountView × AccountView × AccountView × ByteSlice × Ptr)
    (h : Input.parse7 input s = .ok r s') : s' = s ∧ s.readU64 input ≥ 7 := by
  unfold Input.parse7 Input.numAccounts rawLoadU64 SolanaM.require at h
  dsimp only [Bind.bind, SolanaM.bind, Pure.pure, SolanaM.pure, SolanaM.fail] at h
  by_cases hn : s.readU64 input ≥ 7
  · simp only [hn, decide_true, ↓reduceIte, SolanaM.pure, AccountView.nextCursor_exact] at h
    cases hsk : Input.skipAccounts _ _ s with
    | err _ _ => rw [hsk] at h; cases h
    | ok _ s1 =>
      rw [hsk] at h; cases h
      exact ⟨Input.skipAccounts_preserves_state _ _ _ _ _ hsk, hn⟩
  · simp [hn, SolanaM.fail] at h

private theorem parse8_preserves (input : Ptr) (s s' : SvmState)
    (r : AccountView × AccountView × AccountView × AccountView × AccountView × AccountView × AccountView × AccountView × ByteSlice × Ptr)
    (h : Input.parse8 input s = .ok r s') : s' = s ∧ s.readU64 input ≥ 8 := by
  unfold Input.parse8 Input.numAccounts rawLoadU64 SolanaM.require at h
  dsimp only [Bind.bind, SolanaM.bind, Pure.pure, SolanaM.pure, SolanaM.fail] at h
  by_cases hn : s.readU64 input ≥ 8
  · simp only [hn, decide_true, ↓reduceIte, SolanaM.pure, AccountView.nextCursor_exact] at h
    cases hsk : Input.skipAccounts _ _ s with
    | err _ _ => rw [hsk] at h; cases h
    | ok _ s1 =>
      rw [hsk] at h; cases h
      exact ⟨Input.skipAccounts_preserves_state _ _ _ _ _ hsk, hn⟩
  · simp [hn, SolanaM.fail] at h

/-- Pure-read ABI soundness for `parseStrict1..parseStrict8`:
    every strict parser preserves `SvmState` (`s' = s`), enforces `numAccounts ≥ k`, and
    guarantees `s.mem a_i = ABI.nonDupMarker` (`0xFF`) for EVERY returned `AccountView`! -/
theorem Input.parseStrict1_sound (input : Ptr) (dupErr : UInt64) (s s' : SvmState)
    (a0 : AccountView) (ix : ByteSlice) (pid : Ptr)
    (h : Input.parseStrict1 input dupErr s = .ok (a0, ix, pid) s') :
    s' = s ∧ s.readU64 input ≥ 1 ∧ s.mem a0 = ABI.nonDupMarker := by
  unfold Input.parseStrict1 at h
  obtain ⟨⟨a0', ix', pid'⟩, s1, hp, h1⟩ := step_parse_ok h
  have ⟨hs1, hn⟩ := parse1_preserves input s s1 _ hp; subst hs1
  dsimp only at h1
  obtain ⟨m0, h2⟩ := step_requireNonDup h1
  simp [Pure.pure, SolanaM.pure] at h2; obtain ⟨⟨rfl, _, _⟩, rfl⟩ := h2
  exact ⟨rfl, hn, m0⟩

theorem Input.parseStrict2_sound (input : Ptr) (dupErr : UInt64) (s s' : SvmState)
    (a0 a1 : AccountView) (ix : ByteSlice) (pid : Ptr)
    (h : Input.parseStrict2 input dupErr s = .ok (a0, a1, ix, pid) s') :
    s' = s ∧ s.readU64 input ≥ 2 ∧
    s.mem a0 = ABI.nonDupMarker ∧ s.mem a1 = ABI.nonDupMarker := by
  unfold Input.parseStrict2 at h
  obtain ⟨⟨a0', a1', ix', pid'⟩, s1, hp, h1⟩ := step_parse_ok h
  have ⟨hs1, hn⟩ := parse2_preserves input s s1 _ hp; subst hs1
  dsimp only at h1
  obtain ⟨m0, h1⟩ := step_requireNonDup h1
  obtain ⟨m1, h1⟩ := step_requireNonDup h1
  simp [Pure.pure, SolanaM.pure] at h1; obtain ⟨⟨rfl, rfl, _, _⟩, rfl⟩ := h1
  exact ⟨rfl, hn, m0, m1⟩

theorem Input.parseStrict3_sound (input : Ptr) (dupErr : UInt64) (s s' : SvmState)
    (a0 a1 a2 : AccountView) (ix : ByteSlice) (pid : Ptr)
    (h : Input.parseStrict3 input dupErr s = .ok (a0, a1, a2, ix, pid) s') :
    s' = s ∧ s.readU64 input ≥ 3 ∧
    s.mem a0 = ABI.nonDupMarker ∧ s.mem a1 = ABI.nonDupMarker ∧ s.mem a2 = ABI.nonDupMarker := by
  unfold Input.parseStrict3 at h
  obtain ⟨⟨a0', a1', a2', ix', pid'⟩, s1, hp, h1⟩ := step_parse_ok h
  have ⟨hs1, hn⟩ := parse3_preserves input s s1 _ hp; subst hs1
  dsimp only at h1
  obtain ⟨m0, h1⟩ := step_requireNonDup h1
  obtain ⟨m1, h1⟩ := step_requireNonDup h1
  obtain ⟨m2, h1⟩ := step_requireNonDup h1
  simp [Pure.pure, SolanaM.pure] at h1; obtain ⟨⟨rfl, rfl, rfl, _, _⟩, rfl⟩ := h1
  exact ⟨rfl, hn, m0, m1, m2⟩

theorem Input.parseStrict4_sound (input : Ptr) (dupErr : UInt64) (s s' : SvmState)
    (a0 a1 a2 a3 : AccountView) (ix : ByteSlice) (pid : Ptr)
    (h : Input.parseStrict4 input dupErr s = .ok (a0, a1, a2, a3, ix, pid) s') :
    s' = s ∧ s.readU64 input ≥ 4 ∧
    s.mem a0 = ABI.nonDupMarker ∧ s.mem a1 = ABI.nonDupMarker ∧
    s.mem a2 = ABI.nonDupMarker ∧ s.mem a3 = ABI.nonDupMarker := by
  unfold Input.parseStrict4 at h
  obtain ⟨⟨a0', a1', a2', a3', ix', pid'⟩, s1, hp, h1⟩ := step_parse_ok h
  have ⟨hs1, hn⟩ := parse4_preserves input s s1 _ hp; subst hs1
  dsimp only at h1
  obtain ⟨m0, h1⟩ := step_requireNonDup h1
  obtain ⟨m1, h1⟩ := step_requireNonDup h1
  obtain ⟨m2, h1⟩ := step_requireNonDup h1
  obtain ⟨m3, h1⟩ := step_requireNonDup h1
  simp [Pure.pure, SolanaM.pure] at h1; obtain ⟨⟨rfl, rfl, rfl, rfl, _, _⟩, rfl⟩ := h1
  exact ⟨rfl, hn, m0, m1, m2, m3⟩

theorem Input.parseStrict5_sound (input : Ptr) (dupErr : UInt64) (s s' : SvmState)
    (a0 a1 a2 a3 a4 : AccountView) (ix : ByteSlice) (pid : Ptr)
    (h : Input.parseStrict5 input dupErr s = .ok (a0, a1, a2, a3, a4, ix, pid) s') :
    s' = s ∧ s.readU64 input ≥ 5 ∧
    s.mem a0 = ABI.nonDupMarker ∧ s.mem a1 = ABI.nonDupMarker ∧
    s.mem a2 = ABI.nonDupMarker ∧ s.mem a3 = ABI.nonDupMarker ∧
    s.mem a4 = ABI.nonDupMarker := by
  unfold Input.parseStrict5 at h
  obtain ⟨⟨a0', a1', a2', a3', a4', ix', pid'⟩, s1, hp, h1⟩ := step_parse_ok h
  have ⟨hs1, hn⟩ := parse5_preserves input s s1 _ hp; subst hs1
  dsimp only at h1
  obtain ⟨m0, h1⟩ := step_requireNonDup h1
  obtain ⟨m1, h1⟩ := step_requireNonDup h1
  obtain ⟨m2, h1⟩ := step_requireNonDup h1
  obtain ⟨m3, h1⟩ := step_requireNonDup h1
  obtain ⟨m4, h1⟩ := step_requireNonDup h1
  simp [Pure.pure, SolanaM.pure] at h1; obtain ⟨⟨rfl, rfl, rfl, rfl, rfl, _, _⟩, rfl⟩ := h1
  exact ⟨rfl, hn, m0, m1, m2, m3, m4⟩

theorem Input.parseStrict6_sound (input : Ptr) (dupErr : UInt64) (s s' : SvmState)
    (a0 a1 a2 a3 a4 a5 : AccountView) (ix : ByteSlice) (pid : Ptr)
    (h : Input.parseStrict6 input dupErr s = .ok (a0, a1, a2, a3, a4, a5, ix, pid) s') :
    s' = s ∧ s.readU64 input ≥ 6 ∧
    s.mem a0 = ABI.nonDupMarker ∧ s.mem a1 = ABI.nonDupMarker ∧
    s.mem a2 = ABI.nonDupMarker ∧ s.mem a3 = ABI.nonDupMarker ∧
    s.mem a4 = ABI.nonDupMarker ∧ s.mem a5 = ABI.nonDupMarker := by
  unfold Input.parseStrict6 at h
  obtain ⟨⟨a0', a1', a2', a3', a4', a5', ix', pid'⟩, s1, hp, h1⟩ := step_parse_ok h
  have ⟨hs1, hn⟩ := parse6_preserves input s s1 _ hp; subst hs1
  dsimp only at h1
  obtain ⟨m0, h1⟩ := step_requireNonDup h1
  obtain ⟨m1, h1⟩ := step_requireNonDup h1
  obtain ⟨m2, h1⟩ := step_requireNonDup h1
  obtain ⟨m3, h1⟩ := step_requireNonDup h1
  obtain ⟨m4, h1⟩ := step_requireNonDup h1
  obtain ⟨m5, h1⟩ := step_requireNonDup h1
  simp [Pure.pure, SolanaM.pure] at h1; obtain ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, _, _⟩, rfl⟩ := h1
  exact ⟨rfl, hn, m0, m1, m2, m3, m4, m5⟩

theorem Input.parseStrict7_sound (input : Ptr) (dupErr : UInt64) (s s' : SvmState)
    (a0 a1 a2 a3 a4 a5 a6 : AccountView) (ix : ByteSlice) (pid : Ptr)
    (h : Input.parseStrict7 input dupErr s = .ok (a0, a1, a2, a3, a4, a5, a6, ix, pid) s') :
    s' = s ∧ s.readU64 input ≥ 7 ∧
    s.mem a0 = ABI.nonDupMarker ∧ s.mem a1 = ABI.nonDupMarker ∧
    s.mem a2 = ABI.nonDupMarker ∧ s.mem a3 = ABI.nonDupMarker ∧
    s.mem a4 = ABI.nonDupMarker ∧ s.mem a5 = ABI.nonDupMarker ∧
    s.mem a6 = ABI.nonDupMarker := by
  unfold Input.parseStrict7 at h
  obtain ⟨⟨a0', a1', a2', a3', a4', a5', a6', ix', pid'⟩, s1, hp, h1⟩ := step_parse_ok h
  have ⟨hs1, hn⟩ := parse7_preserves input s s1 _ hp; subst hs1
  dsimp only at h1
  obtain ⟨m0, h1⟩ := step_requireNonDup h1
  obtain ⟨m1, h1⟩ := step_requireNonDup h1
  obtain ⟨m2, h1⟩ := step_requireNonDup h1
  obtain ⟨m3, h1⟩ := step_requireNonDup h1
  obtain ⟨m4, h1⟩ := step_requireNonDup h1
  obtain ⟨m5, h1⟩ := step_requireNonDup h1
  obtain ⟨m6, h1⟩ := step_requireNonDup h1
  simp [Pure.pure, SolanaM.pure] at h1; obtain ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, _, _⟩, rfl⟩ := h1
  exact ⟨rfl, hn, m0, m1, m2, m3, m4, m5, m6⟩

theorem Input.parseStrict8_sound (input : Ptr) (dupErr : UInt64) (s s' : SvmState)
    (a0 a1 a2 a3 a4 a5 a6 a7 : AccountView) (ix : ByteSlice) (pid : Ptr)
    (h : Input.parseStrict8 input dupErr s = .ok (a0, a1, a2, a3, a4, a5, a6, a7, ix, pid) s') :
    s' = s ∧ s.readU64 input ≥ 8 ∧
    s.mem a0 = ABI.nonDupMarker ∧ s.mem a1 = ABI.nonDupMarker ∧
    s.mem a2 = ABI.nonDupMarker ∧ s.mem a3 = ABI.nonDupMarker ∧
    s.mem a4 = ABI.nonDupMarker ∧ s.mem a5 = ABI.nonDupMarker ∧
    s.mem a6 = ABI.nonDupMarker ∧ s.mem a7 = ABI.nonDupMarker := by
  unfold Input.parseStrict8 at h
  obtain ⟨⟨a0', a1', a2', a3', a4', a5', a6', a7', ix', pid'⟩, s1, hp, h1⟩ := step_parse_ok h
  have ⟨hs1, hn⟩ := parse8_preserves input s s1 _ hp; subst hs1
  dsimp only at h1
  obtain ⟨m0, h1⟩ := step_requireNonDup h1
  obtain ⟨m1, h1⟩ := step_requireNonDup h1
  obtain ⟨m2, h1⟩ := step_requireNonDup h1
  obtain ⟨m3, h1⟩ := step_requireNonDup h1
  obtain ⟨m4, h1⟩ := step_requireNonDup h1
  obtain ⟨m5, h1⟩ := step_requireNonDup h1
  obtain ⟨m6, h1⟩ := step_requireNonDup h1
  obtain ⟨m7, h1⟩ := step_requireNonDup h1
  simp [Pure.pure, SolanaM.pure] at h1; obtain ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, _, _⟩, rfl⟩ := h1
  exact ⟨rfl, hn, m0, m1, m2, m3, m4, m5, m6, m7⟩

/-! ### Checked Arithmetic Helpers (Zero Overflow Bugs!) -/

/-- Checked `UInt64` addition: fails with `Err.arithmeticOverflow` on wraparound. -/
@[inline] def checkedAdd64 (a b : UInt64) : SolanaM UInt64 := do
  let sum := a + b
  SolanaM.require (sum >= a) Err.arithmeticOverflow
  return sum

/-- Checked `UInt64` subtraction: fails with `Err.insufficientFunds` (or custom error) on underflow. -/
@[inline] def checkedSub64 (a b : UInt64) (errCode : UInt64 := Err.arithmeticOverflow) : SolanaM UInt64 := do
  SolanaM.require (a >= b) errCode
  return a - b

end LeanSVM
