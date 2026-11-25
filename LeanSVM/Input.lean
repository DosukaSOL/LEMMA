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

end Input

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
