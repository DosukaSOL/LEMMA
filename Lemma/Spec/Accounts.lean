/-
  Lemma.Spec.Accounts — account-validation predicates over the SVM state.

  These are *specifications*: they state, in terms of the serialized input buffer (Solana
  ABI v1, as modelled by `LeanSVM.SvmState`), what it means for an account slot to be signed,
  writable, owned by a program, and so on. `Lemma.Guard` provides the runtime checks and proves
  each check succeeds exactly when its predicate holds.

  Account slot layout (non-duplicate entry), offsets from the slot pointer `acc`:
    +0 dup marker (0xFF = not a duplicate) · +1 is_signer · +2 is_writable · +3 executable
    +8 key (32 B) · +40 owner (32 B) · +72 lamports (u64) · +80 data_len (u64) · +88 data

  Trust assumptions (NOT proven, see docs/specs/trusted-base.md): the Solana runtime serializes
  the input buffer as described above, sets the signer/writable flags truthfully, writes the
  executing program's id after the instruction data, and gives every distinct account exactly
  one non-duplicate slot.
-/
import LeanSVM

namespace Lemma.Spec
open LeanSVM

/-- The slot is a full account entry, not an 8-byte duplicate marker. Reading the fields of a
    duplicate marker as an account would read unrelated bytes. -/
def NonDup (s : SvmState) (acc : AccountView) : Prop := s.readU8 acc = 0xFF

def Signer (s : SvmState) (acc : AccountView) : Prop := s.readU8 (acc + 1) ≠ 0

def Writable (s : SvmState) (acc : AccountView) : Prop := s.readU8 (acc + 2) ≠ 0

/-- Two 32-byte public keys in memory are equal (compared as four little-endian words). -/
def KeyEq (s : SvmState) (p q : Ptr) : Prop :=
  s.readU64 p = s.readU64 q ∧ s.readU64 (p + 8) = s.readU64 (q + 8) ∧
  s.readU64 (p + 16) = s.readU64 (q + 16) ∧ s.readU64 (p + 24) = s.readU64 (q + 24)

instance (s : SvmState) (p q : Ptr) : Decidable (KeyEq s p q) := by
  unfold KeyEq; infer_instance

/-- The account's owner field equals the 32-byte key at `prog` (normally the executing program). -/
def OwnedBy (s : SvmState) (acc : AccountView) (prog : Ptr) : Prop :=
  KeyEq s (AccountView.ownerPtr acc) prog

/-- The account's own key equals the 32-byte key at `k`. -/
def HasKey (s : SvmState) (acc : AccountView) (k : Ptr) : Prop :=
  KeyEq s (AccountView.keyPtr acc) k

/-- The account's data is at least 8 bytes long and starts with the 8-byte tag `tag`.
    LEMMA uses such tags to tell account kinds apart (no type confusion). -/
def HasTag (s : SvmState) (acc : AccountView) (tag : UInt64) : Prop :=
  s.readU64 (acc + ABI.accDataLenOffset) ≥ 8 ∧ s.readU64 (acc + ABI.accDataOffset) = tag

end Lemma.Spec
