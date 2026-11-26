/-
  Lemma.Guard — runtime account checks, each proven equivalent to its `Lemma.Spec` predicate.

  For every guard `g` below:
  * `g … s = .ok () s`       ↔ the predicate holds      (`*_ok_iff`)
  * otherwise `g … s = .err c s` with a fixed error code, and the state is unchanged (`*_err`)
  and `guard_bind_ok` lifts this through `>>=`: if a program that starts with a guard succeeds,
  the guard's predicate held in the initial state. This is how component theorems reach the
  deployed entrypoint rather than a separate model.
-/
import LeanSVM
import Lemma.Spec.Accounts
import Lemma.Errors

namespace Lemma.LErr
open LeanSVM
/-- An account was passed as a duplicate of an earlier account slot. -/
abbrev duplicateAccount : UInt64 := Err.custom 0x4C4D0002
/-- Account data has the wrong kind tag (type confusion attempt or uninitialized account). -/
abbrev wrongAccountKind : UInt64 := Err.custom 0x4C4D0003
end Lemma.LErr

namespace Lemma.Guard
open LeanSVM Lemma.Spec

/-! ### Runtime checks -/

@[inline] def requireNonDup (acc : AccountView) : SolanaM Unit :=
  SolanaM.bind (rawLoadU8 acc) fun b => SolanaM.require (b == 0xFF) LErr.duplicateAccount

@[inline] def requireSigner (acc : AccountView) : SolanaM Unit :=
  SolanaM.bind (rawLoadU8 (acc + 1)) fun b => SolanaM.require (b != 0) Err.missingRequiredSignature

@[inline] def requireWritable (acc : AccountView) : SolanaM Unit :=
  SolanaM.bind (rawLoadU8 (acc + 2)) fun b => SolanaM.require (b != 0) Err.invalidAccountData

/-- 32-byte key comparison (four `u64` words). Used instead of `LeanSVM.pubkeyEq` so that the
    proof does not depend on upstream lemmas that use `bv_decide`. -/
@[inline] def keyEq (p q : Ptr) : SolanaM Bool :=
  SolanaM.bind (rawLoadU64 p) fun a0 => SolanaM.bind (rawLoadU64 q) fun b0 =>
  SolanaM.bind (rawLoadU64 (p + 8)) fun a1 => SolanaM.bind (rawLoadU64 (q + 8)) fun b1 =>
  SolanaM.bind (rawLoadU64 (p + 16)) fun a2 => SolanaM.bind (rawLoadU64 (q + 16)) fun b2 =>
  SolanaM.bind (rawLoadU64 (p + 24)) fun a3 => SolanaM.bind (rawLoadU64 (q + 24)) fun b3 =>
  SolanaM.pure (a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3)

@[inline] def requireOwner (acc : AccountView) (prog : Ptr) : SolanaM Unit :=
  SolanaM.bind (keyEq (AccountView.ownerPtr acc) prog) fun ok => SolanaM.require ok Err.illegalOwner

@[inline] def requireKey (acc : AccountView) (k : Ptr) (code : UInt64) : SolanaM Unit :=
  SolanaM.bind (keyEq (AccountView.keyPtr acc) k) fun ok => SolanaM.require ok code

@[inline] def requireTag (acc : AccountView) (tag : UInt64) : SolanaM Unit :=
  SolanaM.bind (rawLoadU64 (acc + ABI.accDataLenOffset)) fun len =>
  if len ≥ 8 then
    SolanaM.bind (rawLoadU64 (acc + ABI.accDataOffset)) fun t =>
      SolanaM.require (t == tag) LErr.wrongAccountKind
  else SolanaM.fail LErr.wrongAccountKind

/-! ### Proofs -/

theorem keyEq_eq (p q : Ptr) (s : SvmState) :
    keyEq p q s = .ok (decide (KeyEq s p q)) s := by
  simp only [keyEq, SolanaM.bind, rawLoadU64, SolanaM.pure, KeyEq]
  congr 1
  rw [Bool.eq_iff_iff]
  simp [and_assoc]

/-- A guard: a state-preserving check that succeeds iff `P` holds, else fails with `code`. -/
def IsGuard (g : SolanaM Unit) (P : SvmState → Prop) (code : UInt64) : Prop :=
  ∀ s, (P s → g s = .ok () s) ∧ (¬ P s → g s = .err code s)

theorem requireNonDup_guard (acc : AccountView) :
    IsGuard (requireNonDup acc) (NonDup · acc) LErr.duplicateAccount := by
  intro s
  simp only [requireNonDup, SolanaM.bind, rawLoadU8, SolanaM.require, NonDup]
  constructor
  · intro h; simp [h, SolanaM.pure]
  · intro h; simp [h, SolanaM.fail]

theorem requireSigner_guard (acc : AccountView) :
    IsGuard (requireSigner acc) (Signer · acc) Err.missingRequiredSignature := by
  intro s
  simp only [requireSigner, SolanaM.bind, rawLoadU8, SolanaM.require, Signer]
  constructor
  · intro h; simp [h, SolanaM.pure]
  · intro h; simp at h; simp [h, SolanaM.fail]

theorem requireWritable_guard (acc : AccountView) :
    IsGuard (requireWritable acc) (Writable · acc) Err.invalidAccountData := by
  intro s
  simp only [requireWritable, SolanaM.bind, rawLoadU8, SolanaM.require, Writable]
  constructor
  · intro h; simp [h, SolanaM.pure]
  · intro h; simp at h; simp [h, SolanaM.fail]

theorem requireOwner_guard (acc : AccountView) (prog : Ptr) :
    IsGuard (requireOwner acc prog) (OwnedBy · acc prog) Err.illegalOwner := by
  intro s
  simp only [requireOwner, SolanaM.bind, keyEq_eq, SolanaM.require, OwnedBy]
  constructor
  · intro h; simp [h, SolanaM.pure]
  · intro h; simp [h, SolanaM.fail]

theorem requireKey_guard (acc : AccountView) (k : Ptr) (code : UInt64) :
    IsGuard (requireKey acc k code) (HasKey · acc k) code := by
  intro s
  simp only [requireKey, SolanaM.bind, keyEq_eq, SolanaM.require, HasKey]
  constructor
  · intro h; simp [h, SolanaM.pure]
  · intro h; simp [h, SolanaM.fail]

theorem requireTag_guard (acc : AccountView) (tag : UInt64) :
    IsGuard (requireTag acc tag) (HasTag · acc tag) LErr.wrongAccountKind := by
  intro s
  simp only [requireTag, SolanaM.bind, rawLoadU64, SolanaM.require, HasTag]
  constructor
  · rintro ⟨hl, ht⟩; simp [hl, ht, SolanaM.bind, rawLoadU64, SolanaM.pure]
  · intro h
    by_cases hl : s.readU64 (acc + ABI.accDataLenOffset) ≥ 8
    · have ht : ¬ s.readU64 (acc + ABI.accDataOffset) = tag := fun ht => h ⟨hl, ht⟩
      simp [hl, ht, SolanaM.bind, rawLoadU64, SolanaM.fail]
    · simp [hl, SolanaM.fail]

/-- If a program that starts with a guard succeeds, the guard's predicate held initially, and
    the rest of the program ran from the unchanged state. -/
theorem guard_bind_ok {α} {g : SolanaM Unit} {P : SvmState → Prop} {code : UInt64}
    (hg : IsGuard g P code) (k : Unit → SolanaM α) (s s' : SvmState) (v : α)
    (h : SolanaM.bind g k s = .ok v s') : P s ∧ k () s = .ok v s' := by
  by_cases hp : P s
  · refine ⟨hp, ?_⟩
    simp only [SolanaM.bind, (hg s).1 hp] at h
    exact h
  · simp only [SolanaM.bind, (hg s).2 hp] at h
    cases h

/-- A failing guard makes the whole program fail with the guard's code and no state change. -/
theorem guard_bind_err {α} {g : SolanaM Unit} {P : SvmState → Prop} {code : UInt64}
    (hg : IsGuard g P code) (k : Unit → SolanaM α) (s : SvmState) (hp : ¬ P s) :
    SolanaM.bind g k s = .err code s := by
  simp only [SolanaM.bind, (hg s).2 hp]

end Lemma.Guard
