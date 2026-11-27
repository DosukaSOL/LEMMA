/-
  Lemma.Parse — the account-list parsers never change the VM state, and return the slots at the
  expected positions. Needed to lift handler theorems to the deployed entrypoint.
-/
import LeanSVM

namespace Lemma.Parse
open LeanSVM

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

theorem parse5_ok (input : Ptr) (s s' : SvmState)
    (r : AccountView × AccountView × AccountView × AccountView × AccountView × LeanSVM.ByteSlice × Ptr)
    (h : Input.parse5 input s = .ok r s') : s' = s ∧ r.1 = input + 8 := by
  unfold Input.parse5 Input.numAccounts Input.firstAccount at h
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
          have e3 := nextCursor_state _ _ _ _ h3
          split at h
          · rename_i a4 s4 h4
            have e4 := nextCursor_state _ _ _ _ h4
            split at h
            · rename_i a5 s5 h5
              have e5 := nextCursor_state _ _ _ _ h5
              split at h
              · rename_i a6 s6 h6
                have e6 := skipAccounts_state _ _ _ _ _ _ rfl h6
                cases h
                exact ⟨by rw [e6, e5, e4, e3, e2, e1], rfl⟩
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · simp at h

end Lemma.Parse
