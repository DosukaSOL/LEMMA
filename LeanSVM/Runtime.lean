/-
  LeanSVM.Runtime
  Pure executable SVM memory/syscall semantics for Lean 4 formal verification,
  paired with `@[noinline]` hardware intrinsics recognized by the native Lean→sBPF compiler.

  Key design invariant:
  - In Lean 4 proofs: every operation has transparent, axiom-free semantics over `SvmState`.
  - In sBPF codegen: `SvmState` is a zero-cost ghost token (0 registers, 0 memory),
    and every `raw*` / `sys*` primitive compiles directly to 1 sBPF instruction or syscall.
-/
import LeanSVM.Types
import LeanSVM.Sha256
import Std.Tactic.BVDecide

namespace LeanSVM

/-! ### Raw Memory Helpers & Faithful CPI Invocation Model -/

/-- Read a little-endian `UInt32` directly from a raw byte map `mem`. -/
def memReadU32 (mem : UInt64 → UInt8) (addr : UInt64) : UInt32 :=
  let b0 := (mem addr).toUInt32
  let b1 := (mem (addr + 1)).toUInt32
  let b2 := (mem (addr + 2)).toUInt32
  let b3 := (mem (addr + 3)).toUInt32
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

/-- Read a little-endian `UInt64` directly from a raw byte map `mem`. -/
def memReadU64 (mem : UInt64 → UInt8) (addr : UInt64) : UInt64 :=
  (memReadU32 mem addr).toUInt64 ||| ((memReadU32 mem (addr + 4)).toUInt64 <<< 32)

/-- Write a single byte to a raw byte map `mem`. -/
def memWriteU8 (mem : UInt64 → UInt8) (addr : UInt64) (v : UInt8) : UInt64 → UInt8 :=
  fun a => if a == addr then v else mem a

/-- Write a little-endian `UInt64` to a raw byte map `mem`. -/
def memWriteU64 (mem : UInt64 → UInt8) (addr v : UInt64) : UInt64 → UInt8 :=
  let m0 := memWriteU8 mem addr v.toUInt8
  let m1 := memWriteU8 m0 (addr + 1) (v >>> 8).toUInt8
  let m2 := memWriteU8 m1 (addr + 2) (v >>> 16).toUInt8
  let m3 := memWriteU8 m2 (addr + 3) (v >>> 24).toUInt8
  let m4 := memWriteU8 m3 (addr + 4) (v >>> 32).toUInt8
  let m5 := memWriteU8 m4 (addr + 5) (v >>> 40).toUInt8
  let m6 := memWriteU8 m5 (addr + 6) (v >>> 48).toUInt8
  memWriteU8 m6 (addr + 7) (v >>> 56).toUInt8

/-- Copy `n` bytes from `src` to `dst` inside a raw byte map `mem`. -/
def memCopyBytes (mem : UInt64 → UInt8) (dst src : UInt64) : Nat → (UInt64 → UInt8)
  | 0 => mem
  | k + 1 => memCopyBytes (memWriteU8 mem dst (mem src)) (dst + 1) (src + 1) k

/-- Zero `n` bytes starting at `dst` inside a raw byte map `mem`. -/
def memZeroBytes (mem : UInt64 → UInt8) (dst : UInt64) : Nat → (UInt64 → UInt8)
  | 0 => mem
  | k + 1 => memZeroBytes (memWriteU8 mem dst 0) (dst + 1) k

/-- Decoded 56-byte `SolAccountInfo` struct passed to `sol_invoke_signed_c`. -/
structure CpiAccountInfo where
  infoPtr     : UInt64
  keyPtr      : UInt64
  lamportsPtr : UInt64
  dataLen     : UInt64
  dataPtr     : UInt64
  ownerPtr    : UInt64
  isSigner    : Bool
  isWritable  : Bool
  deriving Repr, BEq

/-- Decoded CPI call passed to `sol_invoke_signed_c(ixPtr, infosPtr, infosLen, seedsPtr, seedsLen)`. -/
structure CpiInvocation where
  progKeyPtr : UInt64
  metasPtr   : UInt64
  metasLen   : UInt64
  dataPtr    : UInt64
  dataLen    : UInt64
  infos      : List CpiAccountInfo
  seedsPtr   : UInt64
  seedsLen   : UInt64
  deriving Repr, BEq

/-- Decode `n` consecutive 56-byte `SolAccountInfo` entries starting at `infosPtr`. -/
def decodeCpiInfos (mem : UInt64 → UInt8) (infosPtr : UInt64) : Nat → List CpiAccountInfo
  | 0 => []
  | k + 1 =>
    let info : CpiAccountInfo :=
      { infoPtr     := infosPtr
        keyPtr      := memReadU64 mem infosPtr
        lamportsPtr := memReadU64 mem (infosPtr + 8)
        dataLen     := memReadU64 mem (infosPtr + 16)
        dataPtr     := memReadU64 mem (infosPtr + 24)
        ownerPtr    := memReadU64 mem (infosPtr + 32)
        isSigner    := mem (infosPtr + 48) != 0
        isWritable  := mem (infosPtr + 49) != 0 }
    info :: decodeCpiInfos mem (infosPtr + 56) k

/-- Decode a 40-byte `SolInstruction` + `infosLen` `SolAccountInfo` array from `mem`. -/
def decodeCpiInvocation (mem : UInt64 → UInt8)
    (ixPtr infosPtr infosLen seedsPtr seedsLen : UInt64) : CpiInvocation :=
  { progKeyPtr := memReadU64 mem ixPtr
    metasPtr   := memReadU64 mem (ixPtr + 8)
    metasLen   := memReadU64 mem (ixPtr + 16)
    dataPtr    := memReadU64 mem (ixPtr + 24)
    dataLen    := memReadU64 mem (ixPtr + 32)
    infos      := decodeCpiInfos mem infosPtr infosLen.toNat
    seedsPtr   := seedsPtr
    seedsLen   := seedsLen }

/-- Agave write-protection predicate for one `SolAccountInfo`: only writable accounts may have their
    `lamports` (8B), `owner` (32B), `data_len` (`infoPtr+16` & `lamportsPtr+8`), or `data`
    (up to `dataLen + 10240`, Agave's `MAX_PERMITTED_DATA_INCREASE`) modified by a CPI callee. -/
def cpiAccountWritable (proposedMem : UInt64 → UInt8) (info : CpiAccountInfo) (a : UInt64) : Bool :=
  if !info.isWritable then false
  else
    let newLen := memReadU64 proposedMem (info.infoPtr + 16)
    let maxLen :=
      if newLen > info.dataLen then
        if newLen ≤ info.dataLen + 10240 then newLen else info.dataLen + 10240
      else info.dataLen
    (a - info.lamportsPtr < 8) ||
    (a - info.ownerPtr < 32) ||
    (a - (info.infoPtr + 16) < 8) ||
    (a - (info.lamportsPtr + 8) < 8) ||
    (a - info.dataPtr < maxLen)

/-- Returns `true` iff address `a` lies within a writable account passed in `infos`. -/
def cpiAddrWritable (proposedMem : UInt64 → UInt8) (infos : List CpiAccountInfo) (a : UInt64) : Bool :=
  infos.any (cpiAccountWritable proposedMem · a)

/-- Built-in Agave-faithful CPI handler for canonical Solana programs:
    - **System Program** (`1111...1111`): `Transfer` (op 2), `Allocate` (op 8), `Assign` (op 1)
    - **SPL Token** (`Tokenkeg...`) & **SPL Token-2022** (`TokenzQd...`):
      `TransferChecked` (op 12), `MintTo` (op 7), `Burn` (op 8), `InitializeAccount3` (op 18)
    Returns `(1, mem)` for unknown programs or failed precondition checks.
    Note: Universal proofs over `∀ s : SvmState` quantify over arbitrary `s.cpiHandler`, so
    proving unsound "CPI leaves writable accounts unchanged" theorems is impossible! -/
def defaultCpiHandler (mem : UInt64 → UInt8) (inv : CpiInvocation) : UInt64 × (UInt64 → UInt8) :=
  let w0 := memReadU64 mem inv.progKeyPtr
  let w1 := memReadU64 mem (inv.progKeyPtr + 8)
  let w2 := memReadU64 mem (inv.progKeyPtr + 16)
  let w3 := memReadU64 mem (inv.progKeyPtr + 24)
  let isSystem := (w0 ||| w1 ||| w2 ||| w3) == 0
  let isSplToken :=
    (w0 == 0x93a165d7e1f6dd06 && w1 == 0xac79ebce46e1cbd9 &&
     w2 == 0x91375b5fed85b41c && w3 == 0xa900ff7e85f58c3a) ||
    (w0 == 0xde8f75eee1f6dd06 && w1 == 0xdacd6ce4bc5d4218 &&
     w2 == 0x270db9834dfc1ab6 && w3 == 0xfc8ba1d828f9bdfe)
  if isSystem then
    if inv.dataLen < 4 then (1, mem)
    else
      let op := memReadU32 mem inv.dataPtr
      if op == 2 then
        -- SystemProgram::Transfer(lamports: u64): [from(W), to(W)]
        if inv.dataLen < 12 then (1, mem)
        else match inv.infos with
          | src :: dst :: _ =>
            if !src.isWritable || !dst.isWritable then (1, mem)
            else
              let amt := memReadU64 mem (inv.dataPtr + 4)
              let srcLam := memReadU64 mem src.lamportsPtr
              if srcLam < amt then (1, mem)
              else
                let m1 := memWriteU64 mem src.lamportsPtr (srcLam - amt)
                let dstLam := memReadU64 m1 dst.lamportsPtr
                if dstLam + amt < dstLam then (1, mem)
                else (0, memWriteU64 m1 dst.lamportsPtr (dstLam + amt))
          | _ => (1, mem)
      else if op == 8 then
        -- SystemProgram::Allocate(space: u64): [acc(W)]
        if inv.dataLen < 12 then (1, mem)
        else match inv.infos with
          | acc :: _ =>
            let space := memReadU64 mem (inv.dataPtr + 4)
            if !acc.isWritable || acc.dataLen != 0 || space > 10240 then (1, mem)
            else
              let m1 := memWriteU64 mem (acc.infoPtr + 16) space
              let m2 := memWriteU64 m1 (acc.lamportsPtr + 8) space
              (0, memZeroBytes m2 acc.dataPtr space.toNat)
          | _ => (1, mem)
      else if op == 1 then
        -- SystemProgram::Assign(owner: Pubkey): [acc(W)]
        if inv.dataLen < 36 then (1, mem)
        else match inv.infos with
          | acc :: _ =>
            if !acc.isWritable then (1, mem)
            else (0, memCopyBytes mem acc.ownerPtr (inv.dataPtr + 4) 32)
          | _ => (1, mem)
      else (1, mem)
  else if isSplToken then
    if inv.dataLen < 1 then (1, mem)
    else
      let op := mem inv.dataPtr
      if op == 12 then
        -- SPL Token / Token-2022 TransferChecked(amount: u64, decimals: u8): [src(W), mint, dst(W), auth]
        if inv.dataLen < 10 then (1, mem)
        else match inv.infos with
          | src :: mint :: dst :: _ :: _ =>
            let amt := memReadU64 mem (inv.dataPtr + 1)
            let dec := mem (inv.dataPtr + 9)
            let mintDec := mem (mint.dataPtr + 44)
            if !src.isWritable || !dst.isWritable || mintDec != dec then (1, mem)
            else
              let srcAmt := memReadU64 mem (src.dataPtr + 64)
              if srcAmt < amt then (1, mem)
              else
                let m1 := memWriteU64 mem (src.dataPtr + 64) (srcAmt - amt)
                let dstAmt := memReadU64 m1 (dst.dataPtr + 64)
                if dstAmt + amt < dstAmt then (1, mem)
                else (0, memWriteU64 m1 (dst.dataPtr + 64) (dstAmt + amt))
          | _ => (1, mem)
      else if op == 7 then
        -- SPL Token / Token-2022 MintTo(amount: u64): [mint(W), dst(W), auth]
        if inv.dataLen < 9 then (1, mem)
        else match inv.infos with
          | mint :: dst :: _ :: _ =>
            let amt := memReadU64 mem (inv.dataPtr + 1)
            if !mint.isWritable || !dst.isWritable then (1, mem)
            else
              let sup := memReadU64 mem (mint.dataPtr + 36)
              let dstAmt := memReadU64 mem (dst.dataPtr + 64)
              if sup + amt < sup || dstAmt + amt < dstAmt then (1, mem)
              else
                let m1 := memWriteU64 mem (mint.dataPtr + 36) (sup + amt)
                (0, memWriteU64 m1 (dst.dataPtr + 64) (dstAmt + amt))
          | _ => (1, mem)
      else if op == 8 then
        -- SPL Token / Token-2022 Burn(amount: u64): [src(W), mint(W), auth]
        if inv.dataLen < 9 then (1, mem)
        else match inv.infos with
          | src :: mint :: _ :: _ =>
            let amt := memReadU64 mem (inv.dataPtr + 1)
            if !src.isWritable || !mint.isWritable then (1, mem)
            else
              let srcAmt := memReadU64 mem (src.dataPtr + 64)
              let sup := memReadU64 mem (mint.dataPtr + 36)
              if srcAmt < amt || sup < amt then (1, mem)
              else
                let m1 := memWriteU64 mem (src.dataPtr + 64) (srcAmt - amt)
                (0, memWriteU64 m1 (mint.dataPtr + 36) (sup - amt))
          | _ => (1, mem)
      else if op == 18 then
        -- SPL Token / Token-2022 InitializeAccount3(owner: Pubkey): [acc(W), mint]
        if inv.dataLen < 33 then (1, mem)
        else match inv.infos with
          | acc :: mint :: _ =>
            if !acc.isWritable then (1, mem)
            else
              let m1 := memCopyBytes mem acc.dataPtr mint.keyPtr 32
              let m2 := memCopyBytes m1 (acc.dataPtr + 32) (inv.dataPtr + 1) 32
              let m3 := memWriteU64 m2 (acc.dataPtr + 64) 0
              (0, memWriteU8 m3 (acc.dataPtr + 108) 1)
          | _ => (1, mem)
      else (1, mem)
  else (1, mem)

/-- Pure functional model of the Solana Virtual Machine state for kernel-checked proofs. -/
structure SvmState where
  /-- Byte-addressable virtual memory (`addr -> byte`). -/
  mem     : UInt64 → UInt8
  /-- Program log output buffer (newest appended at end). -/
  logs    : List String := []
  /-- Next available stack buffer address (grows downward from `0x200001000`). -/
  stackSp : UInt64 := 0x200001000
  /-- Mock clock slot (used by `sysGetClock` in pure Lean proofs). -/
  slot                : UInt64 := 0
  /-- Mock clock epoch start timestamp (signed i64 bit pattern). -/
  epochStartTimestamp : UInt64 := 0
  /-- Mock clock epoch. -/
  epoch               : UInt64 := 0
  /-- Mock clock leader schedule epoch. -/
  leaderScheduleEpoch : UInt64 := 0
  /-- Mock clock Unix timestamp (signed i64 bit pattern). -/
  unixTimestamp       : UInt64 := 0
  /-- Pluggable CPI callee semantics `(mem, inv) ↦ (rc, proposedMem)` constrained by
      Agave's writable-account writeback boundary in `sysInvokeSignedC`. -/
  cpiHandler : (UInt64 → UInt8) → CpiInvocation → UInt64 × (UInt64 → UInt8) := defaultCpiHandler

namespace SvmState

def empty : SvmState := { mem := fun _ => 0 }

def readU8 (s : SvmState) (addr : UInt64) : UInt8 :=
  s.mem addr

def readU16 (s : SvmState) (addr : UInt64) : UInt16 :=
  let b0 := (s.mem addr).toUInt16
  let b1 := (s.mem (addr + 1)).toUInt16
  b0 ||| (b1 <<< 8)

def readU32 (s : SvmState) (addr : UInt64) : UInt32 :=
  let b0 := (s.mem addr).toUInt32
  let b1 := (s.mem (addr + 1)).toUInt32
  let b2 := (s.mem (addr + 2)).toUInt32
  let b3 := (s.mem (addr + 3)).toUInt32
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

def readU64 (s : SvmState) (addr : UInt64) : UInt64 :=
  let lo := (s.readU32 addr).toUInt64
  let hi := (s.readU32 (addr + 4)).toUInt64
  lo ||| (hi <<< 32)

def writeU8 (s : SvmState) (addr : UInt64) (v : UInt8) : SvmState :=
  { s with mem := fun a => if a == addr then v else s.mem a }

def writeU16 (s : SvmState) (addr : UInt64) (v : UInt16) : SvmState :=
  let s1 := s.writeU8 addr v.toUInt8
  s1.writeU8 (addr + 1) (v >>> 8).toUInt8

def writeU32 (s : SvmState) (addr : UInt64) (v : UInt32) : SvmState :=
  let s1 := s.writeU16 addr v.toUInt16
  s1.writeU16 (addr + 2) (v >>> 16).toUInt16

def writeU64 (s : SvmState) (addr : UInt64) (v : UInt64) : SvmState :=
  let s1 := s.writeU32 addr v.toUInt32
  s1.writeU32 (addr + 4) (v >>> 32).toUInt32

private theorem mem_writeU64_at (s : SvmState) (a v : UInt64) (k : UInt64) :
    (s.writeU64 a v).mem (a + k) =
      if k == 7 then (v >>> 56).toUInt8
      else if k == 6 then (v >>> 48).toUInt8
      else if k == 5 then (v >>> 40).toUInt8
      else if k == 4 then (v >>> 32).toUInt8
      else if k == 3 then (v >>> 24).toUInt8
      else if k == 2 then (v >>> 16).toUInt8
      else if k == 1 then (v >>> 8).toUInt8
      else if k == 0 then v.toUInt8
      else s.mem (a + k) := by
  unfold writeU64 writeU32 writeU16 writeU8
  simp only
  have e7 : (a + k == a + 4 + 2 + 1) = (k == 7) := by bv_decide
  have e6 : (a + k == a + 4 + 2) = (k == 6) := by bv_decide
  have e5 : (a + k == a + 4 + 1) = (k == 5) := by bv_decide
  have e4 : (a + k == a + 4) = (k == 4) := by bv_decide
  have e3 : (a + k == a + 2 + 1) = (k == 3) := by bv_decide
  have e2 : (a + k == a + 2) = (k == 2) := by bv_decide
  have e1 : (a + k == a + 1) = (k == 1) := by bv_decide
  have e0 : (a + k == a) = (k == 0) := by bv_decide
  have b7 : (((v >>> 32).toUInt32 >>> 16).toUInt16 >>> 8).toUInt8 = (v >>> 56).toUInt8 := by bv_decide
  have b6 : ((v >>> 32).toUInt32 >>> 16).toUInt16.toUInt8 = (v >>> 48).toUInt8 := by bv_decide
  have b5 : ((v >>> 32).toUInt32.toUInt16 >>> 8).toUInt8 = (v >>> 40).toUInt8 := by bv_decide
  have b4 : (v >>> 32).toUInt32.toUInt16.toUInt8 = (v >>> 32).toUInt8 := by bv_decide
  have b3 : ((v.toUInt32 >>> 16).toUInt16 >>> 8).toUInt8 = (v >>> 24).toUInt8 := by bv_decide
  have b2 : (v.toUInt32 >>> 16).toUInt16.toUInt8 = (v >>> 16).toUInt8 := by bv_decide
  have b1 : (v.toUInt32.toUInt16 >>> 8).toUInt8 = (v >>> 8).toUInt8 := by bv_decide
  have b0 : v.toUInt32.toUInt16.toUInt8 = v.toUInt8 := by bv_decide
  simp only [e7, e6, e5, e4, e3, e2, e1, e0, b7, b6, b5, b4, b3, b2, b1, b0]

theorem readU64_writeU64_same (s : SvmState) (addr v : UInt64) :
    (s.writeU64 addr v).readU64 addr = v := by
  unfold readU64 readU32
  have p41 : addr + 4 + 1 = addr + 5 := by bv_decide
  have p42 : addr + 4 + 2 = addr + 6 := by bv_decide
  have p43 : addr + 4 + 3 = addr + 7 := by bv_decide
  have p0  : addr + 0 = addr := by bv_decide
  have h0  := mem_writeU64_at s addr v 0
  rw [p0] at h0
  simp only [p41, p42, p43, h0, mem_writeU64_at]
  bv_decide

theorem readU64_writeU64_disjoint (s : SvmState) (a b v : UInt64)
    (h : a + 8 ≤ b ∨ b + 8 ≤ a)
    (ha : a ≤ 0xFFFFFFFFFFFFFFF7) (hb : b ≤ 0xFFFFFFFFFFFFFFF7) :
    (s.writeU64 a v).readU64 b = s.readU64 b := by
  have hmem : ∀ (k : UInt64), k < 8 →
      (s.writeU64 a v).mem (b + k) = s.mem (b + k) := by
    intro k hk
    unfold writeU64 writeU32 writeU16 writeU8
    simp only
    have c7 : (b + k == a + 4 + 2 + 1) = false := by rw [beq_eq_false_iff_ne]; bv_decide
    have c6 : (b + k == a + 4 + 2) = false := by rw [beq_eq_false_iff_ne]; bv_decide
    have c5 : (b + k == a + 4 + 1) = false := by rw [beq_eq_false_iff_ne]; bv_decide
    have c4 : (b + k == a + 4) = false := by rw [beq_eq_false_iff_ne]; bv_decide
    have c3 : (b + k == a + 2 + 1) = false := by rw [beq_eq_false_iff_ne]; bv_decide
    have c2 : (b + k == a + 2) = false := by rw [beq_eq_false_iff_ne]; bv_decide
    have c1 : (b + k == a + 1) = false := by rw [beq_eq_false_iff_ne]; bv_decide
    have c0 : (b + k == a) = false := by rw [beq_eq_false_iff_ne]; bv_decide
    simp [c7, c6, c5, c4, c3, c2, c1, c0]
  unfold readU64 readU32
  have p41 : b + 4 + 1 = b + 5 := by bv_decide
  have p42 : b + 4 + 2 = b + 6 := by bv_decide
  have p43 : b + 4 + 3 = b + 7 := by bv_decide
  have e0 := hmem 0 (by decide)
  have e1 := hmem 1 (by decide)
  have e2 := hmem 2 (by decide)
  have e3 := hmem 3 (by decide)
  have e4 := hmem 4 (by decide)
  have e5 := hmem 5 (by decide)
  have e6 := hmem 6 (by decide)
  have e7 := hmem 7 (by decide)
  have b0 : b + 0 = b := by bv_decide
  rw [b0] at e0
  simp only [p41, p42, p43, e0, e1, e2, e3, e4, e5, e6, e7]

theorem mem_writeU64_outside (s : SvmState) (a x v : UInt64)
    (ha : a ≤ 0xFFFFFFFFFFFFFFF7) (hout : x < a ∨ a + 8 ≤ x) :
    (s.writeU64 a v).mem x = s.mem x := by
  unfold writeU64 writeU32 writeU16 writeU8
  simp only
  have c7 : (x == a + 4 + 2 + 1) = false := by rw [beq_eq_false_iff_ne]; bv_decide
  have c6 : (x == a + 4 + 2) = false := by rw [beq_eq_false_iff_ne]; bv_decide
  have c5 : (x == a + 4 + 1) = false := by rw [beq_eq_false_iff_ne]; bv_decide
  have c4 : (x == a + 4) = false := by rw [beq_eq_false_iff_ne]; bv_decide
  have c3 : (x == a + 2 + 1) = false := by rw [beq_eq_false_iff_ne]; bv_decide
  have c2 : (x == a + 2) = false := by rw [beq_eq_false_iff_ne]; bv_decide
  have c1 : (x == a + 1) = false := by rw [beq_eq_false_iff_ne]; bv_decide
  have c0 : (x == a) = false := by rw [beq_eq_false_iff_ne]; bv_decide
  simp [c7, c6, c5, c4, c3, c2, c1, c0]

end SvmState

/-!
## Hardware Intrinsics (`@[noinline]`)
These exact declarations are recognized by the native Lean→sBPF compiler and lowered
directly to single sBPF instructions / syscalls with zero `SvmState` runtime overhead.
In Lean 4 proofs, they remain completely transparent definitions over `SvmState`.
-/

/-- Result of an SVM step: either error code `err != 0` or `(value, nextState)`. -/
inductive SvmStep (α : Type) where
  | ok (val : α) (st : SvmState)
  | err (code : UInt64) (st : SvmState)

/-- Zero-cost Solana program monad with full executable Lean 4 verification semantics. -/
abbrev SolanaM (α : Type) := SvmState → SvmStep α

namespace SolanaM

@[inline] def pure (a : α) : SolanaM α := fun s => .ok a s

@[inline] def bind (m : SolanaM α) (f : α → SolanaM β) : SolanaM β := fun s =>
  match m s with
  | .ok a s' => f a s'
  | .err c s' => .err c s'

instance : Monad SolanaM where
  pure := SolanaM.pure
  bind := SolanaM.bind

/-- Fail immediately with Solana program error code `code`. -/
@[inline] def fail (code : UInt64) : SolanaM α := fun s => .err code s

/-- Assert condition `cond` or fail with `code`. -/
@[inline] def require (cond : Bool) (code : UInt64) : SolanaM Unit :=
  if cond then pure () else fail code

/-- Run a `SolanaM Unit` entrypoint to a raw Solana `UInt64` exit code (`0` = success). -/
@[inline] def runEntry (m : SolanaM Unit) (s : SvmState) : UInt64 × SvmState :=
  match m s with
  | .ok () s' => (0, s')
  | .err code s' => (code, s')

end SolanaM

/-! ### Low-Level Memory Load / Store Intrinsics -/

@[noinline] def rawLoadU8 (ptr : Ptr) (s : SvmState) : SvmStep UInt8 :=
  .ok (s.readU8 ptr) s

@[noinline] def rawLoadU16 (ptr : Ptr) (s : SvmState) : SvmStep UInt16 :=
  .ok (s.readU16 ptr) s

@[noinline] def rawLoadU32 (ptr : Ptr) (s : SvmState) : SvmStep UInt32 :=
  .ok (s.readU32 ptr) s

@[noinline] def rawLoadU64 (ptr : Ptr) (s : SvmState) : SvmStep UInt64 :=
  .ok (s.readU64 ptr) s

@[noinline] def rawStoreU8 (ptr : Ptr) (val : UInt8) (s : SvmState) : SvmStep Unit :=
  .ok () (s.writeU8 ptr val)

@[noinline] def rawStoreU16 (ptr : Ptr) (val : UInt16) (s : SvmState) : SvmStep Unit :=
  .ok () (s.writeU16 ptr val)

@[noinline] def rawStoreU32 (ptr : Ptr) (val : UInt32) (s : SvmState) : SvmStep Unit :=
  .ok () (s.writeU32 ptr val)

@[noinline] def rawStoreU64 (ptr : Ptr) (val : UInt64) (s : SvmState) : SvmStep Unit :=
  .ok () (s.writeU64 ptr val)

/-! ### Stack Buffer Allocation Intrinsic (Zero Heap Allocation!) -/

/-- Allocate `size` bytes (8-byte aligned) on the sBPF stack frame (`r10 - offset`).
    Compile-time constant `size` folds into a single `mov64 r, r10; add64 r, -off` pair.
    Zero heap usage! -/
@[noinline] def rawStackAlloc (size : UInt64) (s : SvmState) : SvmStep Ptr :=
  let aligned := (size + 7) &&& 0xFFFFFFFFFFFFFFF8
  let nextSp := s.stackSp - aligned
  .ok nextSp { s with stackSp := nextSp }

/-! ### Solana Syscall Intrinsics -/

/-- Emit a UTF-8 log message via `sol_log_(ptr, len)`. String literal lives in `.rodata`. -/
@[noinline] def sysLog (msg : String) (s : SvmState) : SvmStep Unit :=
  .ok () { s with logs := s.logs ++ [msg] }

/-- Emit 5 `UInt64` values via `sol_log_64_(a, b, c, d, e)`. -/
@[noinline] def sysLog64 (a b c d e : UInt64) (s : SvmState) : SvmStep Unit :=
  .ok () { s with logs := s.logs ++ [s!"{a} {b} {c} {d} {e}"] }

/-- Log remaining compute units via `sol_log_compute_units_()`. -/
@[noinline] def sysLogComputeUnits (s : SvmState) : SvmStep Unit :=
  .ok () s

/-- Copy `len` bytes from `src` to `dst` via `sol_memcpy_(dst, src, len)`. -/
@[noinline] def sysMemcpy (dst src len : UInt64) (s : SvmState) : SvmStep Unit :=
  let rec loop (i : Nat) (st : SvmState) : SvmState :=
    match i with
    | 0 => st
    | n + 1 =>
      let off := (len.toNat - (n + 1)).toUInt64
      loop n (st.writeU8 (dst + off) (st.readU8 (src + off)))
  .ok () (loop len.toNat s)

/-- Fill `len` bytes at `dst` with `val` via `sol_memset_(dst, val, len)`. -/
@[noinline] def sysMemset (dst val len : UInt64) (s : SvmState) : SvmStep Unit :=
  let rec loop (i : Nat) (st : SvmState) : SvmState :=
    match i with
    | 0 => st
    | n + 1 =>
      let off := (len.toNat - (n + 1)).toUInt64
      loop n (st.writeU8 (dst + off) val.toUInt8)
  .ok () (loop len.toNat s)

/-- Pure byte-wise lexicographic comparison matching Solana `sol_memcmp_`:
    scans `remaining` bytes starting at `offset`, returning `(lhs - rhs : UInt32)` (the exact
    two's-complement i32 difference) at the first mismatch, or `0` if all bytes are equal. -/
def SvmState.memcmpLoop (s : SvmState) (a b : UInt64) : Nat → UInt64 → UInt32
  | 0, _ => 0
  | n + 1, off =>
    let lhs := s.readU8 (a + off)
    let rhs := s.readU8 (b + off)
    if lhs == rhs then
      s.memcmpLoop a b n (off + 1)
    else
      lhs.toUInt32 - rhs.toUInt32

/-- **THEOREM (`memcmpLoop` Exact Zero-iff-Equal)**:
    `s.memcmpLoop a b n off = 0` iff EVERY byte `i < n` at `a + off + i` equals `b + off + i`. -/
theorem SvmState.memcmpLoop_eq_zero_iff (s : SvmState) (a b : UInt64) (n : Nat) (off : UInt64) :
    s.memcmpLoop a b n off = 0 ↔
    ∀ i : Nat, i < n → s.readU8 (a + (off + UInt64.ofNat i)) = s.readU8 (b + (off + UInt64.ofNat i)) := by
  induction n generalizing off with
  | zero =>
    simp [memcmpLoop]
  | succ k ih =>
    unfold memcmpLoop
    dsimp only
    have h0 : off + UInt64.ofNat 0 = off := by simp [UInt64.ofNat]
    have hStep : ∀ j : Nat, off + 1 + UInt64.ofNat j = off + UInt64.ofNat (j + 1) := by
      intro j
      rw [UInt64.add_assoc]; congr 1
      apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_toNat_eq
      change (1 + j % 2 ^ 64) % 2 ^ 64 = (j + 1) % 2 ^ 64
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_comm]
    by_cases heq : s.readU8 (a + off) = s.readU8 (b + off)
    · have hbeq : (s.readU8 (a + off) == s.readU8 (b + off)) = true := beq_iff_eq.mpr heq
      rw [hbeq]; simp only [↓reduceIte, ih (off + 1)]
      constructor
      · intro hall i hi
        cases i with
        | zero => rwa [h0]
        | succ j =>
          rw [← hStep j]
          exact hall j (Nat.lt_of_succ_lt_succ hi)
      · intro hall j hj
        rw [hStep j]
        exact hall (j + 1) (Nat.succ_lt_succ hj)
    · have hbeq : (s.readU8 (a + off) == s.readU8 (b + off)) = false := beq_false_of_ne heq
      rw [hbeq]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hne32 : (s.readU8 (a + off)).toUInt32 - (s.readU8 (b + off)).toUInt32 ≠ 0 := by
        intro hz
        have hsub : ∀ x y : UInt8, x.toUInt32 - y.toUInt32 = 0 → x = y := by intro x y; bv_decide
        exact heq (hsub _ _ hz)
      constructor
      · intro hz; exact absurd hz hne32
      · intro hall
        have hzero := hall 0 (Nat.zero_lt_succ k)
        rw [h0] at hzero
        exact absurd hzero heq

/-- Compare `len` bytes at `a` and `b`, storing signed i32 first-byte difference at `resultPtr`,
    via `sol_memcmp_`. -/
@[noinline] def sysMemcmp (a b len resultPtr : UInt64) (s : SvmState) : SvmStep Unit :=
  .ok () (s.writeU32 resultPtr (s.memcmpLoop a b len.toNat 0))

/-- Read `n` consecutive bytes starting at `addr`. -/
def SvmState.readBytes (s : SvmState) (addr : UInt64) : Nat → List UInt8
  | 0 => []
  | k + 1 => s.readU8 addr :: s.readBytes (addr + 1) k

/-- Write a byte list sequentially starting at `addr`. -/
def SvmState.writeBytes (s : SvmState) (addr : UInt64) : List UInt8 → SvmState
  | [] => s
  | b :: bs => (s.writeU8 addr b).writeBytes (addr + 1) bs

/-- Read and concatenate `n` Solana `SolBytes` slice descriptors `(ptr: u64, len: u64)` at `valsPtr`. -/
def SvmState.readSliceVec (s : SvmState) (valsPtr : UInt64) : Nat → List UInt8
  | 0 => []
  | k + 1 =>
    let ptr := s.readU64 valsPtr
    let len := s.readU64 (valsPtr + 8)
    s.readBytes ptr len.toNat ++ s.readSliceVec (valsPtr + 16) k

theorem SvmState.writeBytes_mem_outside (s : SvmState) (addr : UInt64) (bs : List UInt8) (x : UInt64)
    (hnoWrap : addr.toNat + bs.length ≤ 2 ^ 64)
    (hout : x.toNat < addr.toNat ∨ addr.toNat + bs.length ≤ x.toNat) :
    (s.writeBytes addr bs).mem x = s.mem x := by
  induction bs generalizing s addr with
  | nil => rfl
  | cons b rest ih =>
    simp only [SvmState.writeBytes, List.length_cons] at hnoWrap hout ⊢
    have hltMax : addr.toNat + 1 < 2 ^ 64 ∨ addr.toNat + 1 = 2 ^ 64 := by omega
    have hneq : x ≠ addr := by
      intro h; subst h; omega
    have hbeq : (x == addr) = false := beq_false_of_ne hneq
    cases rest with
    | nil =>
      simp [SvmState.writeBytes, SvmState.writeU8, hneq]
    | cons b2 rest2 =>
      have h1 : (addr + 1).toNat = addr.toNat + 1 := by
        rw [UInt64.toNat_add]
        have : (1 : UInt64).toNat = 1 := rfl
        rw [this, Nat.mod_eq_of_lt (by simp at hnoWrap; omega)]
      have hnoWrap' : (addr + 1).toNat + (b2 :: rest2).length ≤ 2 ^ 64 := by
        rw [h1]; simp at hnoWrap ⊢; omega
      have hout' : x.toNat < (addr + 1).toNat ∨ (addr + 1).toNat + (b2 :: rest2).length ≤ x.toNat := by
        rw [h1]; simp at hout ⊢; omega
      rw [ih (s.writeU8 addr b) (addr + 1) hnoWrap' hout']
      simp [SvmState.writeU8, hneq]

theorem SvmState.readBytes_writeBytes_same (s : SvmState) (addr : UInt64) (bs : List UInt8)
    (hnoWrap : addr.toNat + bs.length ≤ 2 ^ 64) :
    (s.writeBytes addr bs).readBytes addr bs.length = bs := by
  induction bs generalizing s addr with
  | nil => rfl
  | cons b rest ih =>
    simp only [SvmState.writeBytes, SvmState.readBytes, List.length_cons] at hnoWrap ⊢
    cases rest with
    | nil =>
      simp [SvmState.writeBytes, SvmState.readBytes, SvmState.readU8, SvmState.writeU8]
    | cons b2 rest2 =>
      have h1 : (addr + 1).toNat = addr.toNat + 1 := by
        rw [UInt64.toNat_add]
        have : (1 : UInt64).toNat = 1 := rfl
        rw [this, Nat.mod_eq_of_lt (by simp at hnoWrap; omega)]
      have hnoWrap' : (addr + 1).toNat + (b2 :: rest2).length ≤ 2 ^ 64 := by
        rw [h1]; simp at hnoWrap ⊢; omega
      have hhead : ((s.writeU8 addr b).writeBytes (addr + 1) (b2 :: rest2)).readU8 addr = b := by
        unfold SvmState.readU8
        rw [SvmState.writeBytes_mem_outside (s.writeU8 addr b) (addr + 1) (b2 :: rest2) addr hnoWrap'
              (Or.inl (by rw [h1]; omega))]
        simp [SvmState.writeU8]
      rw [hhead, ih (s.writeU8 addr b) (addr + 1) hnoWrap']

/-- Compute byte-exact FIPS 180-4 SHA-256 over `valsLen` `(ptr, len)` slice descriptors at `valsPtr`,
    writing all 32 digest bytes into `resultPtr`, via `sol_sha256`.
    Returns error code `1` without mutating memory on null `resultPtr`, null `valsPtr` with
    `valsLen > 0`, or `valsLen > 20000` (Agave `HASH_BYTES_MAX_SLICES`). -/
@[noinline] def sysSha256 (valsPtr valsLen resultPtr : UInt64) (s : SvmState) : SvmStep UInt64 :=
  if resultPtr == 0 || (valsLen != 0 && valsPtr == 0) || valsLen > 20000 then
    .ok 1 s
  else
    let msg := s.readSliceVec valsPtr valsLen.toNat
    let digest := Sha256.hash msg
    .ok 0 (s.writeBytes resultPtr digest)

/-- **THEOREM (`sysSha256_spec` — Null-Safety, Exact 32-Byte FIPS 180-4 Digest & Frame)**:
    1. Null `resultPtr = 0` returns `.ok 1 s` without mutating memory.
    2. For valid non-wrapping `resultPtr` and `valsLen ≤ 20000`, `sysSha256` returns `.ok 0 s'`
       where `s'.readBytes resultPtr 32 = Sha256.hash (s.readSliceVec valsPtr valsLen.toNat)`
       and every byte outside `[resultPtr, resultPtr + 32)` is preserved unchanged! -/
theorem sysSha256_spec (valsPtr valsLen resultPtr : UInt64) (s : SvmState) :
    (resultPtr = 0 → sysSha256 valsPtr valsLen resultPtr s = .ok 1 s) ∧
    (resultPtr ≠ 0 → (valsLen = 0 ∨ valsPtr ≠ 0) → valsLen ≤ 20000 →
      resultPtr.toNat + 32 ≤ 2 ^ 64 →
      ∃ s', sysSha256 valsPtr valsLen resultPtr s = .ok 0 s' ∧
        s'.readBytes resultPtr 32 = Sha256.hash (s.readSliceVec valsPtr valsLen.toNat) ∧
        ∀ x : UInt64, (x.toNat < resultPtr.toNat ∨ resultPtr.toNat + 32 ≤ x.toNat) →
          s'.mem x = s.mem x) := by
  constructor
  · intro h0; subst h0; simp [sysSha256]
  · intro hres hvp hlen hnoWrap
    have hcond : (resultPtr == 0 || (valsLen != 0 && valsPtr == 0) || valsLen > 20000) = false := by
      have h1 : (resultPtr == 0) = false := beq_false_of_ne hres
      have h2 : (valsLen != 0 && valsPtr == 0) = false := by
        rcases hvp with hv0 | hpn
        · subst hv0; rfl
        · simp [beq_false_of_ne hpn]
      have h3 : decide (valsLen > 20000) = false :=
        decide_eq_false (UInt64.not_lt.mpr hlen)
      simp [h1, h2, h3]
    unfold sysSha256
    rw [hcond]; simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨_, rfl, ?_, ?_⟩
    · have hlen32 : (Sha256.hash (s.readSliceVec valsPtr valsLen.toNat)).length = 32 :=
        Sha256.hash_length _
      have hnw : resultPtr.toNat + (Sha256.hash (s.readSliceVec valsPtr valsLen.toNat)).length ≤ 2 ^ 64 := by
        rw [hlen32]; exact hnoWrap
      have hrb := SvmState.readBytes_writeBytes_same s resultPtr
        (Sha256.hash (s.readSliceVec valsPtr valsLen.toNat)) hnw
      rwa [hlen32] at hrb
    · intro x hout
      have hlen32 : (Sha256.hash (s.readSliceVec valsPtr valsLen.toNat)).length = 32 :=
        Sha256.hash_length _
      exact SvmState.writeBytes_mem_outside s resultPtr _ x
        (by rw [hlen32]; exact hnoWrap) (by rw [hlen32]; exact hout)

set_option maxRecDepth 20000 in
/-- **THEOREM (`sysSha256_multislice_and_distinct_same_ptr`)**:
    Closes Issue #3 directly:
    1. Hashing multi-slice `["ab", "c"]` through `sysSha256` produces all 32 bytes of NIST `SHA-256("abc")`.
    2. Hashing two DIFFERENT byte payloads stored at the EXACT SAME pointer address produces
       DIFFERENT 32-byte digests (no pointer-only collision, and bytes `8..32` are written!). -/
theorem sysSha256_multislice_and_distinct_same_ptr :
    let descPtr : UInt64 := 0x200000100
    let dataA   : UInt64 := 0x200000200
    let dataB   : UInt64 := 0x200000210
    let outPtr  : UInt64 := 0x200000300
    -- State 1: two slices ["ab", "c"]
    let s1 : SvmState :=
      ((((((SvmState.empty.writeBytes dataA [0x61, 0x62]).writeBytes dataB [0x63]).writeU64
        descPtr dataA).writeU64 (descPtr + 8) 2).writeU64 (descPtr + 16) dataB).writeU64 (descPtr + 24) 1)
    -- State 2: same slice pointer `dataA`, different bytes ["ab", "d"]!
    let s2 : SvmState := s1.writeU8 dataB 0x64
    (match sysSha256 descPtr 2 outPtr s1 with
     | .ok 0 s1' =>
       s1'.readBytes outPtr 32 ==
         [0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
          0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
          0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
          0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad]
     | _ => false) = true ∧
    (match sysSha256 descPtr 2 outPtr s1, sysSha256 descPtr 2 outPtr s2 with
     | .ok 0 s1', .ok 0 s2' =>
       (s1'.readBytes outPtr 32 != s2'.readBytes outPtr 32) &&
       (s1'.readU8 (outPtr + 31) == 0xad)
     | _, _ => false) = true := by
  exact ⟨rfl, rfl⟩

/-- Read the Solana Clock sysvar (40 bytes: `slot`, `epoch_start_timestamp`, `epoch`,
    `leader_schedule_epoch`, `unix_timestamp`) into `outPtr` via `sol_get_clock_sysvar`.
    Returns error code `1` without mutating memory when `outPtr == 0`. -/
@[noinline] def sysGetClock (outPtr : UInt64) (s : SvmState) : SvmStep UInt64 :=
  if outPtr == 0 then
    .ok 1 s
  else
    let s1 := s.writeU64 outPtr        s.slot
    let s2 := s1.writeU64 (outPtr + 8)  s.epochStartTimestamp
    let s3 := s2.writeU64 (outPtr + 16) s.epoch
    let s4 := s3.writeU64 (outPtr + 24) s.leaderScheduleEpoch
    let s5 := s4.writeU64 (outPtr + 32) s.unixTimestamp
    .ok 0 s5

/-- **THEOREM (`sysGetClock` Null-Pointer Safety & Full 40-Byte Spec)**:
    1. `sysGetClock 0 s = .ok 1 s` (returns error without mutating memory).
    2. For valid non-wrapping `outPtr ≠ 0`, `sysGetClock outPtr s` returns `.ok 0 s'`
       writing ALL 5 `Clock` fields (`slot`, `epochStartTimestamp`, `epoch`,
       `leaderScheduleEpoch`, `unixTimestamp`) at offsets `0, 8, 16, 24, 32`. -/
theorem sysGetClock_spec (outPtr : UInt64) (s : SvmState) :
    (outPtr = 0 → sysGetClock outPtr s = .ok 1 s) ∧
    (outPtr ≠ 0 → outPtr ≤ 0xFFFFFFFFFFFFFFD7 →
      ∃ s', sysGetClock outPtr s = .ok 0 s' ∧
        s'.readU64 outPtr = s.slot ∧
        s'.readU64 (outPtr + 8) = s.epochStartTimestamp ∧
        s'.readU64 (outPtr + 16) = s.epoch ∧
        s'.readU64 (outPtr + 24) = s.leaderScheduleEpoch ∧
        s'.readU64 (outPtr + 32) = s.unixTimestamp) := by
  constructor
  · intro h0; subst h0; rfl
  · intro hne hle
    have hbeq : (outPtr == 0) = false := beq_false_of_ne hne
    unfold sysGetClock; rw [hbeq]; simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [SvmState.readU64_writeU64_disjoint _ _ _ _ (Or.inr (by bv_decide)) (by bv_decide) (by bv_decide),
          SvmState.readU64_writeU64_disjoint _ _ _ _ (Or.inr (by bv_decide)) (by bv_decide) (by bv_decide),
          SvmState.readU64_writeU64_disjoint _ _ _ _ (Or.inr (by bv_decide)) (by bv_decide) (by bv_decide),
          SvmState.readU64_writeU64_disjoint _ _ _ _ (Or.inr (by bv_decide)) (by bv_decide) (by bv_decide),
          SvmState.readU64_writeU64_same]
    · rw [SvmState.readU64_writeU64_disjoint _ _ _ _ (Or.inr (by bv_decide)) (by bv_decide) (by bv_decide),
          SvmState.readU64_writeU64_disjoint _ _ _ _ (Or.inr (by bv_decide)) (by bv_decide) (by bv_decide),
          SvmState.readU64_writeU64_disjoint _ _ _ _ (Or.inr (by bv_decide)) (by bv_decide) (by bv_decide),
          SvmState.readU64_writeU64_same]
    · rw [SvmState.readU64_writeU64_disjoint _ _ _ _ (Or.inr (by bv_decide)) (by bv_decide) (by bv_decide),
          SvmState.readU64_writeU64_disjoint _ _ _ _ (Or.inr (by bv_decide)) (by bv_decide) (by bv_decide),
          SvmState.readU64_writeU64_same]
    · rw [SvmState.readU64_writeU64_disjoint _ _ _ _ (Or.inr (by bv_decide)) (by bv_decide) (by bv_decide),
          SvmState.readU64_writeU64_same]
    · rw [SvmState.readU64_writeU64_same]

/-- Cross-program invocation via `sol_invoke_signed_c`.
    Decodes `SolInstruction` and all `infosLen` `SolAccountInfo` structs from `s.mem`,
    invokes `s.cpiHandler`, and commits memory updates strictly within Agave's
    writable-account writeback boundary (`cpiAddrWritable`). -/
@[noinline] def sysInvokeSignedC (ixPtr infosPtr infosLen seedsPtr seedsLen : UInt64)
    (s : SvmState) : SvmStep UInt64 :=
  if ixPtr == 0 || (infosLen != 0 && infosPtr == 0) || infosLen > 255 then
    .ok 1 s
  else
    let inv := decodeCpiInvocation s.mem ixPtr infosPtr infosLen seedsPtr seedsLen
    let (rc, proposedMem) := s.cpiHandler s.mem inv
    if rc != 0 then
      .ok rc s
    else
      .ok 0 { s with mem := fun a =>
        if cpiAddrWritable proposedMem inv.infos a then proposedMem a else s.mem a }

/-- **THEOREM (`sysInvokeSignedC_preserves_non_writable` — Universal Agave Write-Protection Frame)**:
    For ANY `s : SvmState` (quantified over ALL possible `s.cpiHandler` callees — even adversarial
    unknown programs!), if `sysInvokeSignedC` succeeds with `(rc, s')`, then:
    - If `rc ≠ 0`, `s' = s` (failed CPI mutates nothing).
    - If `rc = 0`, EVERY address `a` outside the writable `SolAccountInfo` fields (read-only
      accounts, stack buffers, and non-CPI accounts) satisfies `s'.mem a = s.mem a`! -/
theorem sysInvokeSignedC_preserves_non_writable
    (ixPtr infosPtr infosLen seedsPtr seedsLen : UInt64) (s s' : SvmState) (rc : UInt64)
    (hstep : sysInvokeSignedC ixPtr infosPtr infosLen seedsPtr seedsLen s = .ok rc s') :
    (rc ≠ 0 → s' = s) ∧
    (∀ a : UInt64,
      let inv := decodeCpiInvocation s.mem ixPtr infosPtr infosLen seedsPtr seedsLen
      let proposedMem := (s.cpiHandler s.mem inv).2
      cpiAddrWritable proposedMem inv.infos a = false →
      s'.mem a = s.mem a) := by
  unfold sysInvokeSignedC at hstep
  split at hstep
  · cases hstep
    exact ⟨fun _ => rfl, fun _ _ => rfl⟩
  · dsimp only at hstep
    split at hstep
    · cases hstep
      exact ⟨fun _ => rfl, fun _ _ => rfl⟩
    · cases hstep
      constructor
      · intro hne; exact absurd rfl hne
      · intro a inv proposedMem hnw
        dsimp only at hnw ⊢
        rw [hnw]
        rfl

/-- **THEOREM (`sysInvokeSignedC_readonly_account_preserved`)**:
    Corollary of `sysInvokeSignedC_preserves_non_writable`: if EVERY `SolAccountInfo` in a CPI
    call has `isWritable = false`, then `s'.mem = s.mem` for ALL `cpiHandler`s. -/
theorem sysInvokeSignedC_readonly_account_preserved
    (ixPtr infosPtr infosLen seedsPtr seedsLen : UInt64) (s s' : SvmState) (rc : UInt64)
    (hstep : sysInvokeSignedC ixPtr infosPtr infosLen seedsPtr seedsLen s = .ok rc s')
    (hro : ∀ info ∈ (decodeCpiInvocation s.mem ixPtr infosPtr infosLen seedsPtr seedsLen).infos,
      info.isWritable = false) :
    ∀ a : UInt64, s'.mem a = s.mem a := by
  intro a
  have hframe := (sysInvokeSignedC_preserves_non_writable ixPtr infosPtr infosLen seedsPtr seedsLen s s' rc hstep).2 a
  apply hframe
  unfold cpiAddrWritable
  rw [List.any_eq_false]
  intro info hmem
  simp [cpiAccountWritable, hro info hmem]

set_option maxRecDepth 20000 in
/-- **THEOREM (`sysInvokeSignedC_spl_transfer_mutates_balances`)**:
    Closes Issue #4 directly: under `defaultCpiHandler`, an SPL Token `TransferChecked` CPI
    of `300` tokens from `src` (balance `1000`) to `dst` (balance `50`) genuinely mutates
    `src.data[64..72]` to `700` and `dst.data[64..72]` to `350` while preserving read-only `mint`!
    Therefore NO unsound Lean proof can claim `sysInvokeSignedC` leaves token balances unchanged! -/
theorem sysInvokeSignedC_spl_transfer_mutates_balances :
    let tokKeyPtr : UInt64 := 0x200000000
    let ixPtr     : UInt64 := 0x200000040
    let dataPtr   : UInt64 := 0x200000080
    let infosPtr  : UInt64 := 0x200000100
    let srcAcc    : UInt64 := 0x400000100
    let mintAcc   : UInt64 := 0x400000300
    let dstAcc    : UInt64 := 0x400000500
    let authAcc   : UInt64 := 0x400000700
    -- Write canonical SPL Token program ID at `tokKeyPtr`
    let s0 := ((((SvmState.empty.writeU64 tokKeyPtr 0x93a165d7e1f6dd06).writeU64
      (tokKeyPtr + 8) 0xac79ebce46e1cbd9).writeU64 (tokKeyPtr + 16) 0x91375b5fed85b41c).writeU64
      (tokKeyPtr + 24) 0xa900ff7e85f58c3a)
    -- Write SolInstruction `[tokKeyPtr, 0, 4, dataPtr, 10]` and TransferChecked `[12, 300u64, 6u8]`
    let s1 := (((((s0.writeU64 ixPtr tokKeyPtr).writeU64 (ixPtr + 16) 4).writeU64
      (ixPtr + 24) dataPtr).writeU64 (ixPtr + 32) 10).writeU8 dataPtr 12)
    let s2 := ((s1.writeU64 (dataPtr + 1) 300).writeU8 (dataPtr + 9) 6)
    -- Initialize account data: src amount = 1000, mint decimals = 6, dst amount = 50
    let s3 := (((s2.writeU64 (srcAcc + 88 + 64) 1000).writeU8 (mintAcc + 88 + 44) 6).writeU64
      (dstAcc + 88 + 64) 50)
    -- Helper to write one 56B SolAccountInfo (dataLen = 165, isWritable = w)
    let writeInfo (st : SvmState) (ip acc : UInt64) (w : UInt8) : SvmState :=
      ((((((st.writeU64 ip (acc + 8)).writeU64 (ip + 8) (acc + 72)).writeU64 (ip + 16) 165).writeU64
        (ip + 24) (acc + 88)).writeU64 (ip + 32) (acc + 40)).writeU8 (ip + 49) w)
    let s4 := writeInfo (writeInfo (writeInfo (writeInfo s3 infosPtr srcAcc 1)
      (infosPtr + 56) mintAcc 0) (infosPtr + 112) dstAcc 1) (infosPtr + 168) authAcc 0
    (match sysInvokeSignedC ixPtr infosPtr 4 0 0 s4 with
    | .ok 0 s' =>
      (s'.readU64 (srcAcc + 88 + 64) == 700) &&
      (s'.readU64 (dstAcc + 88 + 64) == 350) &&
      (s'.readU8 (mintAcc + 88 + 44) == 6)
    | _ => false) = true := by
  rfl

set_option maxRecDepth 20000 in
/-- **THEOREM (`sysInvokeSignedC_system_allocate_and_assign`)**:
    Under `defaultCpiHandler`, `SystemProgram::Allocate` updates `data_len` at BOTH
    `SolAccountInfo+16` and `AccountView+80` (zeroing newly allocated bytes), and
    `SystemProgram::Assign` updates the 32-byte `owner` at `acc+40`! -/
theorem sysInvokeSignedC_system_allocate_and_assign :
    let sysKeyPtr : UInt64 := 0x200000000 -- 32 zero bytes = System Program
    let ixPtr     : UInt64 := 0x200000040
    let dataPtr   : UInt64 := 0x200000080
    let infosPtr  : UInt64 := 0x200000100
    let pdaAcc    : UInt64 := 0x400000200
    -- Write dirty byte at pdaAcc.data[0] to confirm Allocate zeroes it
    let s0 := SvmState.empty.writeU8 (pdaAcc + 88) 0xAB
    -- Write SolAccountInfo for pdaAcc (dataLen = 0, writable = 1)
    let s1 := (((((s0.writeU64 infosPtr (pdaAcc + 8)).writeU64 (infosPtr + 8) (pdaAcc + 72)).writeU64
      (infosPtr + 16) 0).writeU64 (infosPtr + 24) (pdaAcc + 88)).writeU64 (infosPtr + 32) (pdaAcc + 40)).writeU8
      (infosPtr + 49) 1
    -- Allocate(space = 64): ixData = [8u32, 64u64] (12 bytes)
    let sAlloc := (((((s1.writeU64 ixPtr sysKeyPtr).writeU64 (ixPtr + 16) 1).writeU64
      (ixPtr + 24) dataPtr).writeU64 (ixPtr + 32) 12).writeU32 dataPtr 8).writeU64 (dataPtr + 4) 64
    (match sysInvokeSignedC ixPtr infosPtr 1 0 0 sAlloc with
    | .ok 0 sAfterAlloc =>
      -- Assign(newOwner = 0x1122334455667788 at word 0): ixData = [1u32, newOwner32] (36 bytes)
      let sAssign := (((sAfterAlloc.writeU64 (ixPtr + 32) 36).writeU32 dataPtr 1).writeU64
        (dataPtr + 4) 0x1122334455667788)
      match sysInvokeSignedC ixPtr infosPtr 1 0 0 sAssign with
      | .ok 0 sFinal =>
        (sAfterAlloc.readU64 (infosPtr + 16) == 64) &&
        (sAfterAlloc.readU64 (pdaAcc + 80) == 64) &&
        (sAfterAlloc.readU8 (pdaAcc + 88) == 0) &&
        (sFinal.readU64 (pdaAcc + 40) == 0x1122334455667788)
      | _ => false
    | _ => false) = true := by
  rfl

/-! ### Ergonomic `SolanaM` Wrappers -/

@[inline] def loadU8  (ptr : Ptr) (off : UInt64 := 0) : SolanaM UInt8  := rawLoadU8  (ptr + off)
@[inline] def loadU16 (ptr : Ptr) (off : UInt64 := 0) : SolanaM UInt16 := rawLoadU16 (ptr + off)
@[inline] def loadU32 (ptr : Ptr) (off : UInt64 := 0) : SolanaM UInt32 := rawLoadU32 (ptr + off)
@[inline] def loadU64 (ptr : Ptr) (off : UInt64 := 0) : SolanaM UInt64 := rawLoadU64 (ptr + off)

@[inline] def storeU8  (ptr : Ptr) (off : UInt64) (v : UInt8)  : SolanaM Unit := rawStoreU8  (ptr + off) v
@[inline] def storeU16 (ptr : Ptr) (off : UInt64) (v : UInt16) : SolanaM Unit := rawStoreU16 (ptr + off) v
@[inline] def storeU32 (ptr : Ptr) (off : UInt64) (v : UInt32) : SolanaM Unit := rawStoreU32 (ptr + off) v
@[inline] def storeU64 (ptr : Ptr) (off : UInt64) (v : UInt64) : SolanaM Unit := rawStoreU64 (ptr + off) v

@[inline] def stackAlloc (size : UInt64) : SolanaM Ptr := rawStackAlloc size
@[inline] def log (msg : String) : SolanaM Unit := sysLog msg
@[inline] def log64 (a b c d e : UInt64) : SolanaM Unit := sysLog64 a b c d e
@[inline] def logComputeUnits : SolanaM Unit := sysLogComputeUnits
@[inline] def memcpy (dst src len : UInt64) : SolanaM Unit := sysMemcpy dst src len
@[inline] def memset (dst val len : UInt64) : SolanaM Unit := sysMemset dst val len
@[inline] def sha256 (valsPtr valsLen resultPtr : UInt64) : SolanaM UInt64 := sysSha256 valsPtr valsLen resultPtr
@[inline] def getClock (outPtr : UInt64) : SolanaM UInt64 := sysGetClock outPtr

end LeanSVM
