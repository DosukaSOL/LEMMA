/-
  Lemma.Examples.GuardedCounter — a minimal program that uses every `Lemma.Guard` check. It shows
  the account-validation layer end to end (compiled, attacked, proven); it is not a component of
  the library.

  Accounts:  0. authority  [signer]
             1. counter    [writable], owned by this program
  Counter data (48 bytes): [0..8) kind tag `TAG` · [8..40) authority key · [40..48) count (u64)
  Instruction data: none. Effect: count := count + 1 (checked).
-/
import LeanSVM
import Lemma.Guard

namespace Lemma.Examples.GuardedCounter
open LeanSVM Lemma.Guard Lemma.Spec

/-- Account-kind tag for counter accounts: ASCII "LMCOUNTR" read as little-endian `u64`. -/
abbrev TAG : UInt64 := 0x52544E554F434D4C
abbrev DATA_LEN : UInt64 := 48

def entrypoint (input : Ptr) : SolanaM Unit := do
  let (auth, counter, _ix, progId) ← Input.parse2 input
  requireNonDup auth
  requireNonDup counter
  requireSigner auth
  requireWritable counter
  requireOwner counter progId
  requireTag counter TAG
  let len ← AccountView.dataLen counter
  SolanaM.require (len == DATA_LEN) Err.invalidAccountData
  -- the stored authority must be the signer
  let okAuth ← keyEq (AccountView.dataPtr counter + 8) (AccountView.keyPtr auth)
  SolanaM.require okAuth Err.illegalOwner
  let n ← AccountView.readDataU64 counter 40
  let n' ← checkedAdd64 n 1
  AccountView.writeDataU64 counter 40 n'

/-! ### Entrypoint-level theorem

The guards are proven on their own in `Lemma.Guard`. Here the guarantee is lifted to the deployed
`entrypoint`: on any input and state where it succeeds, the authority slot was a non-duplicate
signer, and the counter slot was a non-duplicate, writable, program-owned account of the right
kind. -/

namespace Proofs
open LeanSVM Lemma.Guard Lemma.Spec

theorem nextCursor_state (acc : AccountView) (s s' : SvmState) (p : Ptr)
    (h : AccountView.nextCursor acc s = .ok p s') : s' = s := by
  unfold AccountView.nextCursor at h
  simp only [Bind.bind, SolanaM.bind, rawLoadU8] at h
  split at h <;> cases h <;> rfl

theorem skipAccounts_state : ∀ (n : Nat) (c rem : UInt64) (s s' : SvmState) (p : Ptr),
    rem.toNat = n → Input.skipAccounts c rem s = .ok p s' → s' = s := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih
  · intro c rem s s' p hn h
    rw [Input.skipAccounts] at h
    by_cases h0 : rem = 0
    · simp only [h0, ↓reduceDIte] at h
      simp only [Pure.pure, SolanaM.pure] at h; cases h; rfl
    · simp only [h0, ↓reduceDIte] at h
      simp only [Bind.bind, SolanaM.bind] at h
      split at h
      · rename_i q s1 hq
        have e1 := nextCursor_state c s s1 q hq
        have hlt : (rem - 1).toNat < n := by
          have : rem.toNat ≠ 0 := fun hz => h0 (UInt64.toNat_inj.mp (by rw [hz]; rfl))
          rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by show 1 ≤ _; omega))]
          show rem.toNat - 1 < n; omega
        rw [ih _ hlt q (rem - 1) s1 s' p rfl h, e1]
      · cases h

theorem parse2_ok (input : Ptr) (s s' : SvmState) (r : AccountView × AccountView × LeanSVM.ByteSlice × Ptr)
    (h : Input.parse2 input s = .ok r s') : s' = s ∧ r.1 = input + 8 := by
  unfold Input.parse2 Input.numAccounts Input.firstAccount at h
  simp only [Bind.bind, SolanaM.bind, rawLoadU64, SolanaM.require, Pure.pure, SolanaM.pure] at h
  split at h
  · rename_i u0 s0 h0
    have e0 : s0 = s := by
      split at h0
      · simp only [SolanaM.pure] at h0; cases h0; rfl
      · simp [SolanaM.fail] at h0
    subst e0
    split at h
    · rename_i a1 s1 h1
      have e1 := nextCursor_state _ _ _ _ h1
      split at h
      · rename_i a2 s2 h2
        have e2 := nextCursor_state _ _ _ _ h2
        split at h
        · rename_i a3 s3 h3
          have e3 := skipAccounts_state _ _ _ _ _ _ rfl h3
          cases h
          exact ⟨by rw [e3, e2, e1], rfl⟩
        · cases h
      · cases h
    · cases h
  · simp at h

/-- **Deployed-entrypoint theorem.** Whenever `entrypoint` succeeds, every account check held
    in the initial state, for the slots the program actually used. -/
theorem entrypoint_checks (input : Ptr) (s s' : SvmState)
    (h : entrypoint input s = .ok () s') :
    ∃ counter progId : Ptr,
      NonDup s (input + 8) ∧ Signer s (input + 8) ∧
      NonDup s counter ∧ Writable s counter ∧ OwnedBy s counter progId ∧ HasTag s counter TAG := by
  unfold entrypoint at h
  simp only [Bind.bind] at h
  unfold SolanaM.bind at h
  split at h
  · rename_i r s1 hp
    obtain ⟨rfl, hauth⟩ := parse2_ok input s s1 r hp
    obtain ⟨auth, counter, ix, progId⟩ := r
    have hauth' : auth = input + 8 := hauth
    subst hauth'
    obtain ⟨h1, h⟩ := guard_bind_ok (requireNonDup_guard _) _ _ _ _ h
    obtain ⟨h2, h⟩ := guard_bind_ok (requireNonDup_guard _) _ _ _ _ h
    obtain ⟨h3, h⟩ := guard_bind_ok (requireSigner_guard _) _ _ _ _ h
    obtain ⟨h4, h⟩ := guard_bind_ok (requireWritable_guard _) _ _ _ _ h
    obtain ⟨h5, h⟩ := guard_bind_ok (requireOwner_guard _ _) _ _ _ _ h
    obtain ⟨h6, -⟩ := guard_bind_ok (requireTag_guard _ _) _ _ _ _ h
    exact ⟨counter, progId, h1, h3, h2, h4, h5, h6⟩
  · cases h

end Proofs
end Lemma.Examples.GuardedCounter
