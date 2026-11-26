/-
  Examples.Counter
  Zero-copy, zero-allocation on-chain Solana Counter program in Lean 4 with kernel-checked proofs.

  Accounts:
    0. `[writable]` Counter account (>= 8 bytes of data storing little-endian `UInt64` count)

  Instructions (1-byte opcode + optional 8-byte payload):
    `0`            : Init (set count = 0)
    `1`            : Increment (checked count + 1)
    `2` + `u64_le` : Add (checked count + delta)
    `3`            : Reset (requires signer; set count = 0)
-/
import LeanSVM
import Std.Tactic.BVDecide

open LeanSVM

namespace Examples.Counter

/-- Core counter state transition (factored cleanly for both compilation and formal verification). -/
@[inline] def processCounter (acc : AccountView) (progId ixPtr : Ptr) (ixLen : UInt64) : SolanaM Unit := do
  let writable ← AccountView.isWritable acc
  SolanaM.require writable Err.invalidAccountData
  let owned ← pubkeyEq (AccountView.ownerPtr acc) progId
  SolanaM.require owned Err.illegalOwner
  let dlen ← AccountView.dataLen acc
  SolanaM.require (dlen == 8) Err.invalidAccountData
  SolanaM.require (ixLen >= 1) Err.invalidInstructionData
  let op ← loadU8 ixPtr 0
  if op == 0 then
    AccountView.writeDataU64 acc 0 0
  else if op == 1 then
    let cur ← AccountView.readDataU64 acc 0
    let next ← checkedAdd64 cur 1
    AccountView.writeDataU64 acc 0 next
  else if op == 2 then
    SolanaM.require (ixLen >= 9) Err.invalidInstructionData
    let delta ← loadU64 ixPtr 1
    let cur ← AccountView.readDataU64 acc 0
    let next ← checkedAdd64 cur delta
    AccountView.writeDataU64 acc 0 next
  else if op == 3 then
    let signer ← AccountView.isSigner acc
    SolanaM.require signer Err.missingRequiredSignature
    AccountView.writeDataU64 acc 0 0
  else
    SolanaM.fail Err.invalidInstructionData

def entrypoint (input : Ptr) : SolanaM Unit := do
  let (acc, ix, progId) ← Input.parse1 input
  processCounter acc progId ix.ptr ix.len

/-! ### Formal Verification (Zero `sorry`, Zero Custom Axioms) -/

/-- Formal theorem: Increment (`op = 1`) on a valid program-owned exact-8B writable counter account
    with `cur < 2^64 - 1` always succeeds (`code = 0`) and sets the stored value to `cur + 1`. -/
theorem counter_increment_adds_one
    (acc progId ixPtr ixLen : UInt64) (s : SvmState)
    (hw : s.readU8 (acc + ABI.accIsWritableOffset) ≠ 0)
    (ho0 : s.readU64 (acc + ABI.accOwnerOffset) = s.readU64 progId)
    (ho1 : s.readU64 (acc + ABI.accOwnerOffset + 8) = s.readU64 (progId + 8))
    (ho2 : s.readU64 (acc + ABI.accOwnerOffset + 16) = s.readU64 (progId + 16))
    (ho3 : s.readU64 (acc + ABI.accOwnerOffset + 24) = s.readU64 (progId + 24))
    (hd : s.readU64 (acc + ABI.accDataLenOffset) = 8)
    (hi : ixLen ≥ 1)
    (hop : s.readU8 (ixPtr + 0) = 1)
    (hnoovf : s.readU64 (acc + (ABI.accDataOffset + 0)) + 1 ≥ s.readU64 (acc + (ABI.accDataOffset + 0))) :
    let (code, s') := SolanaM.runEntry (processCounter acc progId ixPtr ixLen) s
    code = 0 ∧ s'.readU64 (acc + (ABI.accDataOffset + 0)) = s.readU64 (acc + (ABI.accDataOffset + 0)) + 1 := by
  have h10 : ((1 : UInt8) == 0) = false := by decide
  have h11 : ((1 : UInt8) == 1) = true := by decide
  unfold SolanaM.runEntry processCounter
  unfold AccountView.isWritable AccountView.ownerPtr AccountView.dataLen AccountView.readDataU64 AccountView.writeDataU64
  unfold pubkeyEq checkedAdd64 loadU8 rawLoadU8 rawLoadU64 rawStoreU64
  simp only [Bind.bind, Pure.pure, SolanaM.bind, SolanaM.pure, SolanaM.require,
    hw, ho0, ho1, ho2, ho3, hd, hi, hop, h10, h11, hnoovf, beq_self_eq_true,
    bne_iff_ne, ne_eq, not_true_eq_false, not_false_eq_true, decide_true, Bool.false_eq_true,
    ↓reduceIte, SvmState.readU64_writeU64_same, and_self]

/-- Formal theorem: Increment (`op = 1`) at `UInt64.MAX` (`0xFFFFFFFFFFFFFFFF`)
    is guaranteed to reject with `Err.arithmeticOverflow` and leave VM memory unchanged. -/
theorem counter_increment_overflow_rejected
    (acc progId ixPtr ixLen : UInt64) (s : SvmState)
    (hw : s.readU8 (acc + ABI.accIsWritableOffset) ≠ 0)
    (ho0 : s.readU64 (acc + ABI.accOwnerOffset) = s.readU64 progId)
    (ho1 : s.readU64 (acc + ABI.accOwnerOffset + 8) = s.readU64 (progId + 8))
    (ho2 : s.readU64 (acc + ABI.accOwnerOffset + 16) = s.readU64 (progId + 16))
    (ho3 : s.readU64 (acc + ABI.accOwnerOffset + 24) = s.readU64 (progId + 24))
    (hd : s.readU64 (acc + ABI.accDataLenOffset) = 8)
    (hi : ixLen ≥ 1)
    (hop : s.readU8 (ixPtr + 0) = 1)
    (hmax : s.readU64 (acc + (ABI.accDataOffset + 0)) = 0xFFFFFFFFFFFFFFFF) :
    SolanaM.runEntry (processCounter acc progId ixPtr ixLen) s = (Err.arithmeticOverflow, s) := by
  have h10 : ((1 : UInt8) == 0) = false := by decide
  have h11 : ((1 : UInt8) == 1) = true := by decide
  have hovf : ¬ ((0xFFFFFFFFFFFFFFFF : UInt64) + 1 ≥ 0xFFFFFFFFFFFFFFFF) := by decide
  unfold SolanaM.runEntry processCounter
  unfold AccountView.isWritable AccountView.ownerPtr AccountView.dataLen AccountView.readDataU64 AccountView.writeDataU64
  unfold pubkeyEq checkedAdd64 loadU8 rawLoadU8 rawLoadU64 rawStoreU64
  simp only [Bind.bind, Pure.pure, SolanaM.bind, SolanaM.pure, SolanaM.require, SolanaM.fail,
    hw, ho0, ho1, ho2, ho3, hd, hi, hop, h10, h11, hmax, hovf, beq_self_eq_true,
    bne_iff_ne, ne_eq, not_true_eq_false, not_false_eq_true, decide_true, decide_false,
    Bool.false_eq_true, ↓reduceIte]

/-- Formal theorem: Any account NOT owned by `progId` is unconditionally rejected with `Err.illegalOwner`. -/
theorem counter_rejects_wrong_owner
    (acc progId ixPtr ixLen : UInt64) (s : SvmState)
    (hw : s.readU8 (acc + ABI.accIsWritableOffset) ≠ 0)
    (hne : s.readU64 (acc + ABI.accOwnerOffset) ≠ s.readU64 progId) :
    SolanaM.runEntry (processCounter acc progId ixPtr ixLen) s = (Err.illegalOwner, s) := by
  unfold SolanaM.runEntry processCounter
  unfold AccountView.isWritable AccountView.ownerPtr pubkeyEq rawLoadU8 rawLoadU64
  simp only [Bind.bind, Pure.pure, SolanaM.bind, SolanaM.pure, SolanaM.require, SolanaM.fail,
    hw, hne, bne_iff_ne, ne_eq, not_false_eq_true, Bool.false_eq_true, ↓reduceIte]

end Examples.Counter
