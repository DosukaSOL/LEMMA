/-
  Lemma.Mem — kernel-checked lemmas about lean-svm's byte-addressed memory model.

  Upstream's `SvmState.readU64_writeU64_same` / `_disjoint` are proved with `bv_decide`, so they
  depend on native-evaluation axioms and LEMMA's audit policy forbids them. These are
  independent proofs of the same facts using only `propext`, `Classical.choice` and
  `Quot.sound`. They are what lets LEMMA state theorems about the state *after* a program writes
  (balances, configuration) and not only about the checks it performs.
-/
import LeanSVM

namespace Lemma.Mem
open LeanSVM


private theorem or_shl (x y : Nat) (k : Nat) (hx : x < 2 ^ k) : x ||| (y <<< k) = x + y * 2 ^ k := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]; omega

/-- Little-endian value of 4 bytes. -/
theorem readU32_toNat (s : SvmState) (a : UInt64) :
    (s.readU32 a).toNat = (s.mem a).toNat + (s.mem (a+1)).toNat * 2^8 +
      (s.mem (a+2)).toNat * 2^16 + (s.mem (a+3)).toNat * 2^24 := by
  simp only [SvmState.readU32, UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32]
  have h0 := (s.mem a).toNat_lt; have h1 := (s.mem (a+1)).toNat_lt
  have h2 := (s.mem (a+2)).toNat_lt; have h3 := (s.mem (a+3)).toNat_lt
  generalize (s.mem a).toNat = b0 at *
  generalize (s.mem (a+1)).toNat = b1 at *
  generalize (s.mem (a+2)).toNat = b2 at *
  generalize (s.mem (a+3)).toNat = b3 at *
  simp only [show (8 : UInt32).toNat % 32 = 8 from rfl, show (16 : UInt32).toNat % 32 = 16 from rfl,
    show (24 : UInt32).toNat % 32 = 24 from rfl, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega : b1 * 2^8 < 2^32), Nat.mod_eq_of_lt (by omega : b2 * 2^16 < 2^32),
    Nat.mod_eq_of_lt (by omega : b3 * 2^24 < 2^32)]
  rw [← Nat.shiftLeft_eq b1, or_shl _ _ _ (by omega)]
  rw [← Nat.shiftLeft_eq b2, or_shl _ _ _ (by omega)]
  rw [← Nat.shiftLeft_eq b3, or_shl _ _ _ (by omega)]
  simp only [Nat.shiftLeft_eq]

theorem readU64_toNat (s : SvmState) (a : UInt64) :
    (s.readU64 a).toNat = (s.readU32 a).toNat + (s.readU32 (a+4)).toNat * 2^32 := by
  simp only [SvmState.readU64, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64]
  have h0 := (s.readU32 a).toNat_lt; have h1 := (s.readU32 (a+4)).toNat_lt
  generalize (s.readU32 a).toNat = lo at *
  generalize (s.readU32 (a+4)).toNat = hi at *
  simp only [show (32 : UInt64).toNat % 64 = 32 from rfl, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega : hi * 2^32 < 2^64), ← Nat.shiftLeft_eq hi, or_shl _ _ _ (by omega),
    Nat.shiftLeft_eq]

theorem add_eq_add_iff (a c d : UInt64) : a + c = a + d ↔ c = d := by
  constructor
  · intro h; have := congrArg (· - a) h; simpa [UInt64.add_comm a, UInt64.add_sub_cancel] using this
  · intro h; rw [h]

theorem self_eq_add_iff (a c : UInt64) : a = a + c ↔ c = 0 := by
  have := add_eq_add_iff a 0 c; simp only [UInt64.add_zero] at this; rw [this]; exact eq_comm

theorem add_eq_self_iff (a c : UInt64) : a + c = a ↔ c = 0 := by
  rw [eq_comm]; exact self_eq_add_iff a c

theorem readU64_writeU64_same (s : SvmState) (a v : UInt64) : (s.writeU64 a v).readU64 a = v := by
  apply UInt64.toNat_inj.mp
  rw [readU64_toNat, readU32_toNat, readU32_toNat]
  simp only [SvmState.writeU64, SvmState.writeU32, SvmState.writeU16, SvmState.writeU8,
    UInt64.add_assoc, beq_iff_eq, add_eq_add_iff, self_eq_add_iff, add_eq_self_iff]
  simp (config := { decide := true }) only [UInt64.reduceAdd, ite_true, ite_false]
  simp only [UInt16.toNat_toUInt8, UInt32.toNat_toUInt16, UInt64.toNat_toUInt32,
    UInt16.toNat_shiftRight, UInt32.toNat_shiftRight, UInt64.toNat_shiftRight,
    show UInt16.toNat 8 % 16 = 8 from rfl, show UInt32.toNat 16 % 32 = 16 from rfl,
    show UInt64.toNat 32 % 64 = 32 from rfl, Nat.shiftRight_eq_div_pow]
  have := v.toNat_lt
  omega

/-- Two 8-byte ranges `[a, a+8)` and `[b, b+8)` do not overlap (modulo 2^64). -/
def Disjoint8 (a b : UInt64) : Prop := 8 ≤ (b - a).toNat ∧ 8 ≤ (a - b).toNat

theorem ne_of_disjoint8 {a b : UInt64} (h : Disjoint8 a b) (i j : UInt64) (hi : i.toNat < 8)
    (hj : j.toNat < 8) : b + i ≠ a + j := by
  intro he
  have he' := congrArg UInt64.toNat he
  simp only [UInt64.toNat_add] at he'
  obtain ⟨h1, h2⟩ := h
  rw [UInt64.toNat_sub] at h1 h2
  have := a.toNat_lt; have := b.toNat_lt
  omega

theorem mem_writeU64_of_ne (s : SvmState) (a v x : UInt64)
    (h : ∀ j : UInt64, j.toNat < 8 → x ≠ a + j) : (s.writeU64 a v).mem x = s.mem x := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide)
  have h3 := h 3 (by decide); have h4 := h 4 (by decide); have h5 := h 5 (by decide)
  have h6 := h 6 (by decide); have h7 := h 7 (by decide)
  simp only [UInt64.add_zero] at h0
  simp only [SvmState.writeU64, SvmState.writeU32, SvmState.writeU16, SvmState.writeU8,
    UInt64.add_assoc, beq_iff_eq]
  simp (config := { decide := true }) only [UInt64.reduceAdd, h0, h1, h2, h3, h4, h5, h6, h7,
    ite_false]

theorem readU64_writeU64_disjoint (s : SvmState) (a b v : UInt64) (h : Disjoint8 a b) :
    (s.writeU64 a v).readU64 b = s.readU64 b := by
  have key : ∀ i : UInt64, i.toNat < 8 → (s.writeU64 a v).mem (b + i) = s.mem (b + i) :=
    fun i hi => mem_writeU64_of_ne s a v (b + i) (fun j hj => ne_of_disjoint8 h i j hi hj)
  have k0 := key 0 (by decide); simp only [UInt64.add_zero] at k0
  have k1 := key 1 (by decide); have k2 := key 2 (by decide); have k3 := key 3 (by decide)
  have k4 := key 4 (by decide); have k5 := key 5 (by decide); have k6 := key 6 (by decide)
  have k7 := key 7 (by decide)
  simp only [SvmState.readU64, SvmState.readU32, UInt64.add_assoc]
  simp only [UInt64.reduceAdd, k0, k1, k2, k3, k4, k5, k6, k7]


theorem disjoint8_comm {a b : UInt64} (h : Disjoint8 a b) : Disjoint8 b a := ⟨h.2, h.1⟩

end Lemma.Mem
