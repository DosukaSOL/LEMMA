/-
  Lemma.Components.FeeSplitterProofs — theorems about the deployed fee-splitter code.

  * `split_dust_bound` — pure arithmetic: if the shares sum to 10000 bps, then recipient 0's
    "remainder" share lies between its own floor share and that floor + 2. The dust is at most
    2 lamports.
  * `splitIx_spec` — whenever the on-chain `Split` handler succeeds: every validation check
    held, the shares sum exactly to `amount`, each balance changed by exactly its share, the vault
    kept its reserve, and the total lamports of the four accounts are conserved.
  * `initIx_spec` — whenever `Init` succeeds: every check held, the vault was uninitialized
    (re-initialization is impossible), the configured shares sum to 10000, the reserve was
    covered, and the vault is now tagged as initialized.
  * `entrypoint_dispatch` — whenever the entrypoint succeeds, it ran exactly one of the two
    handlers on the parsed accounts, from the initial state.
-/
import Lemma.Components.FeeSplitter
import Lemma.Mem

namespace Lemma.Components.FeeSplitter.Proofs
open LeanSVM Lemma.Guard Lemma.Spec Lemma.Math Lemma.Mem Lemma.Parse
open Lemma.Components.FeeSplitter

/-- Lamport balance of the account in slot `a`. -/
def lam (s : SvmState) (a : AccountView) : Nat := (s.readU64 (a + offLamports)).toNat
/-- A `u64` configuration field of the vault. -/
def cfg (s : SvmState) (vault : AccountView) (off : UInt64) : Nat := (s.readU64 (vault + off)).toNat

/-- Rounding dust: with shares summing to 10000 bps, `A − ⌊A·b1/10000⌋ − ⌊A·b2/10000⌋` lies
    in `[⌊A·b0/10000⌋, ⌊A·b0/10000⌋ + 2]`, and the two floor shares never exceed `A`. -/
theorem split_dust_bound (A b0 b1 b2 : Nat) (hsum : b0 + b1 + b2 = 10000) :
    A * b1 / 10000 + A * b2 / 10000 ≤ A ∧
    A * b0 / 10000 ≤ A - (A * b1 / 10000 + A * b2 / 10000) ∧
    A - (A * b1 / 10000 + A * b2 / 10000) ≤ A * b0 / 10000 + 2 := by
  have e : A * b0 + A * b1 + A * b2 = A * 10000 := by rw [← Nat.mul_add, ← Nat.mul_add, hsum]
  have d0 := Nat.div_add_mod (A * b0) 10000
  have d1 := Nat.div_add_mod (A * b1) 10000
  have d2 := Nat.div_add_mod (A * b2) 10000
  have m0 := Nat.mod_lt (A * b0) (show 0 < 10000 by decide)
  have m1 := Nat.mod_lt (A * b1) (show 0 < 10000 by decide)
  have m2 := Nat.mod_lt (A * b2) (show 0 < 10000 by decide)
  omega

private theorem toNat_BPS : BPS.toNat = 10000 := rfl

/-- Nat facts from the on-chain `validBps` check. -/
theorem validBps_toNat {b0 b1 b2 : UInt64} (h : validBps b0 b1 b2 = true) :
    b0.toNat + b1.toNat + b2.toNat = 10000 := by
  simp only [validBps, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, hs⟩ := h
  rw [UInt64.le_iff_toNat_le, toNat_BPS] at h0 h1 h2
  have := congrArg UInt64.toNat hs
  simp only [UInt64.toNat_add, toNat_BPS] at this
  omega

theorem splitIx_spec (auth vault r0 r1 r2 : AccountView) (ixPtr ixLen : UInt64) (progId : Ptr)
    (s s' : SvmState) (h : splitIx auth vault r0 r1 r2 ixPtr ixLen progId s = .ok () s') :
    -- (1) every validation check held in the initial state
    (NonDup s auth ∧ NonDup s vault ∧ NonDup s r0 ∧ NonDup s r1 ∧ NonDup s r2 ∧ Signer s auth ∧
     Writable s vault ∧ Writable s r0 ∧ Writable s r1 ∧ Writable s r2 ∧ OwnedBy s vault progId ∧
     HasTag s vault TAG ∧ HasKey s auth (vault + offAuth) ∧ HasKey s r0 (vault + offR0) ∧
     HasKey s r1 (vault + offR1) ∧ HasKey s r2 (vault + offR2)) ∧
    -- (2) exact accounting
    ∃ amount s0 s1 s2 : Nat,
      amount = (s.readU64 (ixPtr + 1)).toNat ∧
      cfg s vault offBps0 + cfg s vault offBps1 + cfg s vault offBps2 = 10000 ∧
      s1 = amount * cfg s vault offBps1 / 10000 ∧
      s2 = amount * cfg s vault offBps2 / 10000 ∧
      s0 + s1 + s2 = amount ∧
      amount * cfg s vault offBps0 / 10000 ≤ s0 ∧ s0 ≤ amount * cfg s vault offBps0 / 10000 + 2 ∧
      amount ≤ lam s vault ∧
      lam s' vault = lam s vault - amount ∧
      lam s' r0 = lam s r0 + s0 ∧ lam s' r1 = lam s r1 + s1 ∧ lam s' r2 = lam s r2 + s2 ∧
      cfg s vault offReserve ≤ lam s' vault ∧
      lam s' vault + lam s' r0 + lam s' r1 + lam s' r2 =
        lam s vault + lam s r0 + lam s r1 + lam s r2 := by
  unfold splitIx at h
  simp only [Bind.bind] at h
  replace h := guard_bind_ok (requireNonDup_guard _) _ _ _ _ h
  obtain ⟨g1, h⟩ := h
  replace h := guard_bind_ok (requireNonDup_guard _) _ _ _ _ h
  obtain ⟨g2, h⟩ := h
  replace h := guard_bind_ok (requireNonDup_guard _) _ _ _ _ h
  obtain ⟨g3, h⟩ := h
  replace h := guard_bind_ok (requireNonDup_guard _) _ _ _ _ h
  obtain ⟨g4, h⟩ := h
  replace h := guard_bind_ok (requireNonDup_guard _) _ _ _ _ h
  obtain ⟨g5, h⟩ := h
  replace h := guard_bind_ok (requireSigner_guard _) _ _ _ _ h
  obtain ⟨g6, h⟩ := h
  replace h := guard_bind_ok (requireWritable_guard _) _ _ _ _ h
  obtain ⟨g7, h⟩ := h
  replace h := guard_bind_ok (requireWritable_guard _) _ _ _ _ h
  obtain ⟨g8, h⟩ := h
  replace h := guard_bind_ok (requireWritable_guard _) _ _ _ _ h
  obtain ⟨g9, h⟩ := h
  replace h := guard_bind_ok (requireWritable_guard _) _ _ _ _ h
  obtain ⟨g10, h⟩ := h
  replace h := guard_bind_ok (requireOwner_guard _ _) _ _ _ _ h
  obtain ⟨g11, h⟩ := h
  replace h := guard_bind_ok (requireTag_guard _ _) _ _ _ _ h
  obtain ⟨g12, h⟩ := h
  replace h := guard_bind_ok (requireKey_guard _ _ _) _ _ _ _ h
  obtain ⟨g13, h⟩ := h
  replace h := guard_bind_ok (requireKey_guard _ _ _) _ _ _ _ h
  obtain ⟨g14, h⟩ := h
  replace h := guard_bind_ok (requireKey_guard _ _ _) _ _ _ _ h
  obtain ⟨g15, h⟩ := h
  replace h := guard_bind_ok (requireKey_guard _ _ _) _ _ _ _ h
  obtain ⟨g16, h⟩ := h
  replace h := guard_bind_ok (requireDisjoint_guard _ _) _ _ _ _ h
  obtain ⟨dv0, h⟩ := h
  replace h := guard_bind_ok (requireDisjoint_guard _ _) _ _ _ _ h
  obtain ⟨dv1, h⟩ := h
  replace h := guard_bind_ok (requireDisjoint_guard _ _) _ _ _ _ h
  obtain ⟨dv2, h⟩ := h
  replace h := guard_bind_ok (requireDisjoint_guard _ _) _ _ _ _ h
  obtain ⟨d01, h⟩ := h
  replace h := guard_bind_ok (requireDisjoint_guard _ _) _ _ _ _ h
  obtain ⟨d02, h⟩ := h
  replace h := guard_bind_ok (requireDisjoint_guard _ _) _ _ _ _ h
  obtain ⟨d12, h⟩ := h
  simp only [bind_rawLoadU64] at h
  replace h := require_bind_ok h
  obtain ⟨-, h⟩ := h
  replace h := require_bind_ok h
  obtain ⟨-, h⟩ := h
  simp only [bind_rawLoadU64] at h
  replace h := require_bind_ok h
  obtain ⟨hbps, h⟩ := h
  replace h := bind_ok_inv h
  obtain ⟨q1, t1, hm1, h⟩ := h
  obtain ⟨rfl, -, -, hq1⟩ := (mulDivFloorM_ok_iff _ _ _ _ _ _).mp hm1
  replace h := bind_ok_inv h
  obtain ⟨q2, t2, hm2, h⟩ := h
  obtain ⟨rfl, -, -, hq2⟩ := (mulDivFloorM_ok_iff _ _ _ _ _ _).mp hm2
  replace h := bind_ok_inv h
  obtain ⟨q12, t3, hm3, h⟩ := h
  obtain ⟨rfl, hq12⟩ := checkedAdd64_ok hm3
  replace h := bind_ok_inv h
  obtain ⟨q0, t4, hm4, h⟩ := h
  obtain ⟨rfl, hle0, hq0⟩ := checkedSub64_ok hm4
  simp only [bind_rawLoadU64] at h
  replace h := bind_ok_inv h
  obtain ⟨bvNew, t5, hm5, h⟩ := h
  obtain ⟨rfl, hlev, hbv⟩ := checkedSub64_ok hm5
  replace h := require_bind_ok h
  obtain ⟨hres, h⟩ := h
  replace h := bind_ok_inv h
  obtain ⟨n0, t6, hm6, h⟩ := h
  obtain ⟨rfl, hn0⟩ := checkedAdd64_ok hm6
  replace h := bind_ok_inv h
  obtain ⟨n1, t7, hm7, h⟩ := h
  obtain ⟨rfl, hn1⟩ := checkedAdd64_ok hm7
  replace h := bind_ok_inv h
  obtain ⟨n2, t8, hm8, h⟩ := h
  obtain ⟨rfl, hn2⟩ := checkedAdd64_ok hm8

  simp only [bind_rawStoreU64, rawStoreU64] at h
  cases h
  refine ⟨⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16⟩, ?_⟩
  -- read the four balances back from the final state
  have rv : lam (((((t8.writeU64 (vault + offLamports) bvNew).writeU64 (r0 + offLamports) n0).writeU64
      (r1 + offLamports) n1).writeU64 (r2 + offLamports) n2)) vault = bvNew.toNat := by
    unfold lam
    rw [readU64_writeU64_disjoint _ _ _ _ (disjoint8_comm dv2),
      readU64_writeU64_disjoint _ _ _ _ (disjoint8_comm dv1),
      readU64_writeU64_disjoint _ _ _ _ (disjoint8_comm dv0), readU64_writeU64_same]
  have r0' : lam (((((t8.writeU64 (vault + offLamports) bvNew).writeU64 (r0 + offLamports) n0).writeU64
      (r1 + offLamports) n1).writeU64 (r2 + offLamports) n2)) r0 = n0.toNat := by
    unfold lam
    rw [readU64_writeU64_disjoint _ _ _ _ (disjoint8_comm d02),
      readU64_writeU64_disjoint _ _ _ _ (disjoint8_comm d01), readU64_writeU64_same]
  have r1' : lam (((((t8.writeU64 (vault + offLamports) bvNew).writeU64 (r0 + offLamports) n0).writeU64
      (r1 + offLamports) n1).writeU64 (r2 + offLamports) n2)) r1 = n1.toNat := by
    unfold lam
    rw [readU64_writeU64_disjoint _ _ _ _ (disjoint8_comm d12), readU64_writeU64_same]
  have r2' : lam (((((t8.writeU64 (vault + offLamports) bvNew).writeU64 (r0 + offLamports) n0).writeU64
      (r1 + offLamports) n1).writeU64 (r2 + offLamports) n2)) r2 = n2.toNat := by
    unfold lam
    rw [readU64_writeU64_same]
  rw [rv, r0', r1', r2']
  have hsum := validBps_toNat hbps
  rw [toNat_BPS] at hq1 hq2
  obtain ⟨hd1, hd2, hd3⟩ := split_dust_bound (t8.readU64 (ixPtr + 1)).toNat
    (t8.readU64 (vault + offBps0)).toNat (t8.readU64 (vault + offBps1)).toNat
    (t8.readU64 (vault + offBps2)).toNat hsum
  simp only [GE.ge, decide_eq_true_eq, UInt64.le_iff_toNat_le] at hres
  refine ⟨(t8.readU64 (ixPtr + 1)).toNat, q0.toNat, q1.toNat, q2.toNat, rfl, hsum, hq1, hq2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [lam, cfg]) <;> omega

theorem initIx_spec (auth vault r0 r1 r2 : AccountView) (ixPtr ixLen : UInt64) (progId : Ptr)
    (s s' : SvmState) (h : initIx auth vault r0 r1 r2 ixPtr ixLen progId s = .ok () s') :
    (NonDup s auth ∧ NonDup s vault ∧ NonDup s r0 ∧ NonDup s r1 ∧ NonDup s r2 ∧ Signer s auth ∧
     Writable s vault ∧ OwnedBy s vault progId) ∧
    s.readU64 (vault + offTag) = 0 ∧
    s.readU64 (vault + 80) = DATA_LEN ∧
    (s.readU64 (ixPtr + 1)).toNat + (s.readU64 (ixPtr + 9)).toNat +
      (s.readU64 (ixPtr + 17)).toNat = 10000 ∧
    (s.readU64 (ixPtr + 25)).toNat ≤ lam s vault ∧
    s'.readU64 (vault + offTag) = TAG := by
  unfold initIx at h
  simp only [Bind.bind] at h
  replace h := guard_bind_ok (requireNonDup_guard _) _ _ _ _ h
  obtain ⟨g1, h⟩ := h
  replace h := guard_bind_ok (requireNonDup_guard _) _ _ _ _ h
  obtain ⟨g2, h⟩ := h
  replace h := guard_bind_ok (requireNonDup_guard _) _ _ _ _ h
  obtain ⟨g3, h⟩ := h
  replace h := guard_bind_ok (requireNonDup_guard _) _ _ _ _ h
  obtain ⟨g4, h⟩ := h
  replace h := guard_bind_ok (requireNonDup_guard _) _ _ _ _ h
  obtain ⟨g5, h⟩ := h
  replace h := guard_bind_ok (requireSigner_guard _) _ _ _ _ h
  obtain ⟨g6, h⟩ := h
  replace h := guard_bind_ok (requireWritable_guard _) _ _ _ _ h
  obtain ⟨g7, h⟩ := h
  replace h := guard_bind_ok (requireOwner_guard _ _) _ _ _ _ h
  obtain ⟨g8, h⟩ := h
  simp only [bind_rawLoadU64] at h
  replace h := require_bind_ok h
  obtain ⟨hlen, h⟩ := h
  simp only [bind_rawLoadU64] at h
  replace h := require_bind_ok h
  obtain ⟨htag, h⟩ := h
  replace h := require_bind_ok h
  obtain ⟨-, h⟩ := h
  simp only [bind_rawLoadU64] at h
  replace h := require_bind_ok h
  obtain ⟨hbps, h⟩ := h
  simp only [bind_rawLoadU64] at h
  replace h := require_bind_ok h
  obtain ⟨hres, h⟩ := h
  replace h := bind_ok_inv h
  obtain ⟨u, st, -, h⟩ := h
  simp only [rawStoreU64] at h
  cases h
  simp only [beq_iff_eq] at hlen htag
  simp only [GE.ge, decide_eq_true_eq, UInt64.le_iff_toNat_le] at hres
  exact ⟨⟨g1, g2, g3, g4, g5, g6, g7, g8⟩, htag, hlen, validBps_toNat hbps, hres,
    readU64_writeU64_same _ _ _⟩

/-- **Re-initialization is impossible:** `Init` never succeeds on a vault whose kind tag is
    already set (in particular on any vault a previous `Init` initialized). -/
theorem initIx_rejects_initialized (auth vault r0 r1 r2 : AccountView) (ixPtr ixLen : UInt64)
    (progId : Ptr) (s s' : SvmState) (hinit : s.readU64 (vault + offTag) ≠ 0) :
    initIx auth vault r0 r1 r2 ixPtr ixLen progId s ≠ .ok () s' :=
  fun h => hinit (initIx_spec auth vault r0 r1 r2 ixPtr ixLen progId s s' h).2.1

/-- **Deployed entrypoint.** Whenever it succeeds, it ran exactly one handler (`Init` or `Split`)
    from the initial state, with the authority in the first account slot. So `initIx_spec` and
    `splitIx_spec` apply to every successful transaction. -/
theorem entrypoint_dispatch (input : Ptr) (s s' : SvmState)
    (h : entrypoint input s = .ok () s') :
    ∃ (vault r0 r1 r2 : AccountView) (ixPtr ixLen : UInt64) (progId : Ptr),
      initIx (input + 8) vault r0 r1 r2 ixPtr ixLen progId s = .ok () s' ∨
      splitIx (input + 8) vault r0 r1 r2 ixPtr ixLen progId s = .ok () s' := by
  unfold entrypoint at h
  simp only [Bind.bind] at h
  replace h := bind_ok_inv h
  obtain ⟨r, s1, hp, h⟩ := h
  obtain ⟨rfl, hauth⟩ := parse5_ok input s s1 r hp
  obtain ⟨auth, vault, r0, r1, r2, ix, progId⟩ := r
  have ha : auth = input + 8 := hauth
  subst ha
  replace h := require_bind_ok h
  obtain ⟨-, h⟩ := h
  simp only [bind_rawLoadU8] at h
  refine ⟨vault, r0, r1, r2, ix.ptr, ix.len, progId, ?_⟩
  split at h
  · exact Or.inl h
  · split at h
    · exact Or.inr h
    · simp [SolanaM.fail] at h

end Lemma.Components.FeeSplitter.Proofs
