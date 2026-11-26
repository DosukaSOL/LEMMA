/-
  LeanSVM.CPI
  Zero-heap, stack-allocated Solana Cross-Program Invocation (`sol_invoke_signed_c`)
  for SPL Token, SPL Token-2022, and the Solana System Program.

  Exact C ABI layouts verified against Agave `solana-program-runtime 3.1.3`:
  - `SolInstruction`  (40 bytes): `[program_id_addr, accounts_addr, accounts_len, data_addr, data_len]`
  - `SolAccountMeta`  (16 bytes): `[pubkey_addr, is_writable:u8, is_signer:u8, pad:6]`
  - `SolAccountInfo`  (56 bytes): `[key, lamports, data_len, data, owner, rent_epoch, is_signer, is_writable, exec, pad:5]`
  - `SolSignerSeedC`  (16 bytes): `[addr, len]`
  - `SolSignerSeedsC` (16 bytes): `[seeds_addr, seeds_len]`
-/
import LeanSVM.Types
import LeanSVM.Runtime
import LeanSVM.Input
import Std.Tactic.BVDecide

namespace LeanSVM.CPI

/-- Write one 16-byte `SolAccountMeta` into `metaPtr`. -/
@[inline] def writeMeta (metaPtr : Ptr) (acc : AccountView) (writable signer : UInt8) : SolanaM Unit := do
  storeU64 metaPtr 0 (AccountView.keyPtr acc)
  storeU8  metaPtr 8 writable
  storeU8  metaPtr 9 signer

/-- Write one 56-byte `SolAccountInfo` into `infoPtr` directly from a zero-copy `AccountView`.
    Outlined as a 1-CU internal sBPF helper so multi-CPI DeFi programs share one tiny 13-insn copy! -/
@[noinline] def writeAccountInfo (infoPtr : Ptr) (acc : AccountView) : SolanaM Unit := do
  let dlen ← AccountView.dataLen acc
  let isSig ← rawLoadU8 (acc + ABI.accIsSignerOffset)
  let isWrt ← rawLoadU8 (acc + ABI.accIsWritableOffset)
  let isExe ← rawLoadU8 (acc + ABI.accIsExecutableOffset)
  storeU64 infoPtr 0  (AccountView.keyPtr acc)
  storeU64 infoPtr 8  (acc + ABI.accLamportsOffset)
  storeU64 infoPtr 16 dlen
  storeU64 infoPtr 24 (AccountView.dataPtr acc)
  storeU64 infoPtr 32 (AccountView.ownerPtr acc)
  storeU64 infoPtr 40 0 -- rent_epoch
  storeU8  infoPtr 48 isSig
  storeU8  infoPtr 49 isWrt
  storeU8  infoPtr 50 isExe

/-- Write a 40-byte `SolInstruction` header into `ixPtr`. -/
@[inline] def writeInstruction (ixPtr : Ptr) (progKeyPtr metasPtr numMetas dataPtr dataLen : UInt64) :
    SolanaM Unit := do
  storeU64 ixPtr 0  progKeyPtr
  storeU64 ixPtr 8  metasPtr
  storeU64 ixPtr 16 numMetas
  storeU64 ixPtr 24 dataPtr
  storeU64 ixPtr 32 dataLen

/-! ### SPL Token & SPL Token-2022 CPIs (Identical ABI for both Token & Token-2022!) -/

/-- Shared outlined 5-arg `TransferChecked` CPI executor (compiled ONCE per binary!).
    `accs4Ptr` points to 4 `AccountView`s `[source, mint, dest, auth]` on caller's stack;
    `signersPtr` is `0` for unsigned CPI or pointer to a 1-element `SolSignerSeedsC`! -/
@[noinline] private def cpiExecTransferChecked (tokProg : AccountView) (accs4Ptr : Ptr)
    (amount : UInt64) (decimals : UInt8) (signersPtr : Ptr) : SolanaM Unit := do
  let source    ← loadU64 accs4Ptr 0
  let mint      ← loadU64 accs4Ptr 8
  let dest      ← loadU64 accs4Ptr 16
  let authority ← loadU64 accs4Ptr 24
  let buf ← stackAlloc 344
  let metas := buf + 40
  let infos := buf + 104
  let data  := buf + 328
  storeU8  data 0 12
  storeU64 data 1 amount
  storeU8  data 9 decimals
  writeMeta metas        source    1 0
  writeMeta (metas + 16) mint      0 0
  writeMeta (metas + 32) dest      1 0
  writeMeta (metas + 48) authority 0 1
  writeAccountInfo infos         source
  writeAccountInfo (infos + 56)  mint
  writeAccountInfo (infos + 112) dest
  writeAccountInfo (infos + 168) authority
  writeInstruction buf (AccountView.keyPtr tokProg) metas 4 data 10
  let signersLen : UInt64 := if signersPtr == 0 then 0 else 1
  let rc ← sysInvokeSignedC buf infos 4 signersPtr signersLen
  SolanaM.require (rc == 0) rc

/-- Invoke SPL Token OR SPL Token-2022 `TransferChecked` (opcode 12) WITHOUT PDA signing.
    Zero heap allocation; shares ONE outlined `cpiExecTransferChecked` across the whole `.so`! -/
@[inline] def tokenTransferChecked (tokenProg source mint dest authority : AccountView)
    (amount : UInt64) (decimals : UInt8) : SolanaM Unit := do
  let accs4 ← stackAlloc 32
  storeU64 accs4 0  source
  storeU64 accs4 8  mint
  storeU64 accs4 16 dest
  storeU64 accs4 24 authority
  cpiExecTransferChecked tokenProg accs4 amount decimals 0

/-- Invoke SPL Token OR SPL Token-2022 `TransferChecked` (opcode 12) WITH a 3-seed PDA signer
    `[tag(4B), keySeed(32B), bump(1B)]`! Shares ONE outlined `cpiExecTransferChecked`! -/
@[inline] def tokenTransferCheckedSigned (tokenProg source mint dest pdaAuthority : AccountView)
    (amount : UInt64) (decimals : UInt8)
    (tagU32 : UInt32) (keySeedPtr : Ptr) (bump : UInt8) : SolanaM Unit := do
  -- 32B accs4 + 8B seedBuf + 48B seedsArr + 16B signersArr = 104 bytes on caller stack!
  let sbuf ← stackAlloc 104
  storeU64 sbuf 0  source
  storeU64 sbuf 8  mint
  storeU64 sbuf 16 dest
  storeU64 sbuf 24 pdaAuthority
  let seedBuf    := sbuf + 32
  let seedsArr   := sbuf + 40
  let signersArr := sbuf + 88
  storeU32 seedBuf 0 tagU32
  storeU8  seedBuf 4 bump
  storeU64 seedsArr 0  seedBuf
  storeU64 seedsArr 8  4
  storeU64 seedsArr 16 keySeedPtr
  storeU64 seedsArr 24 32
  storeU64 seedsArr 32 (seedBuf + 4)
  storeU64 seedsArr 40 1
  storeU64 signersArr 0 seedsArr
  storeU64 signersArr 8 3
  cpiExecTransferChecked tokenProg sbuf amount decimals signersArr

/-- Shared outlined 5-arg `MintTo` PDA-signed CPI executor (compiled ONCE per binary!). -/
@[noinline] private def cpiExecMintTo (tokProg : AccountView) (accs3Ptr : Ptr)
    (amount : UInt64) (signersPtr : Ptr) : SolanaM Unit := do
  let mint         ← loadU64 accs3Ptr 0
  let dest         ← loadU64 accs3Ptr 8
  let pdaAuthority ← loadU64 accs3Ptr 16
  let buf ← stackAlloc 272
  let metas := buf + 40
  let infos := buf + 88
  let data  := buf + 256
  storeU8  data 0 7
  storeU64 data 1 amount
  writeMeta metas        mint         1 0
  writeMeta (metas + 16) dest         1 0
  writeMeta (metas + 32) pdaAuthority 0 1
  writeAccountInfo infos         mint
  writeAccountInfo (infos + 56)  dest
  writeAccountInfo (infos + 112) pdaAuthority
  writeInstruction buf (AccountView.keyPtr tokProg) metas 3 data 9
  let rc ← sysInvokeSignedC buf infos 3 signersPtr 1
  SolanaM.require (rc == 0) rc

/-- Invoke SPL Token OR SPL Token-2022 `MintTo` (opcode 7) WITH a 3-seed PDA signer. -/
@[inline] def tokenMintToSigned (tokenProg mint dest pdaAuthority : AccountView)
    (amount : UInt64) (tagU32 : UInt32) (keySeedPtr : Ptr) (bump : UInt8) : SolanaM Unit := do
  let sbuf ← stackAlloc 96
  storeU64 sbuf 0  mint
  storeU64 sbuf 8  dest
  storeU64 sbuf 16 pdaAuthority
  let seedBuf    := sbuf + 24
  let seedsArr   := sbuf + 32
  let signersArr := sbuf + 80
  storeU32 seedBuf 0 tagU32
  storeU8  seedBuf 4 bump
  storeU64 seedsArr 0  seedBuf
  storeU64 seedsArr 8  4
  storeU64 seedsArr 16 keySeedPtr
  storeU64 seedsArr 24 32
  storeU64 seedsArr 32 (seedBuf + 4)
  storeU64 seedsArr 40 1
  storeU64 signersArr 0 seedsArr
  storeU64 signersArr 8 3
  cpiExecMintTo tokenProg sbuf amount signersArr

/-- Invoke SPL Token OR SPL Token-2022 `Burn` (opcode 8) signed by transaction signer `authority`.
    Stack layout (272 bytes total, 0 heap!). -/
@[noinline] def tokenBurn (tokenProg account mint authority : AccountView) (amount : UInt64) :
    SolanaM Unit := do
  let buf ← stackAlloc 272
  let metas := buf + 40
  let infos := buf + 88
  let data  := buf + 256
  -- Instruction data: `[8, amount_le8]` (9 bytes)
  storeU8  data 0 8
  storeU64 data 1 amount
  -- AccountMetas: [account(W), mint(W), authority(S)]
  writeMeta metas        account   1 0
  writeMeta (metas + 16) mint      1 0
  writeMeta (metas + 32) authority 0 1
  -- AccountInfos
  writeAccountInfo infos         account
  writeAccountInfo (infos + 56)  mint
  writeAccountInfo (infos + 112) authority
  -- SolInstruction
  writeInstruction buf (AccountView.keyPtr tokenProg) metas 3 data 9
  let rc ← sysInvokeSignedC buf infos 3 0 0
  SolanaM.require (rc == 0) rc

/-- Invoke Solana `SystemProgram::Transfer` (opcode 2u32) to transfer `lamports`
    from transaction signer `fromAcc` to `toAcc`.
    Stack layout (200 bytes total, 0 heap!). -/
@[noinline] def systemTransfer (sysProg fromAcc toAcc : AccountView) (lamports : UInt64) :
    SolanaM Unit := do
  let buf ← stackAlloc 200
  let metas := buf + 40
  let infos := buf + 72
  let data  := buf + 184
  -- Instruction data: `[2u32_le, lamports_u64_le]` (12 bytes)
  storeU32 data 0 2
  storeU64 data 4 lamports
  -- AccountMetas: [from(W,S), to(W)]
  writeMeta metas        fromAcc 1 1
  writeMeta (metas + 16) toAcc   1 0
  -- AccountInfos
  writeAccountInfo infos        fromAcc
  writeAccountInfo (infos + 56) toAcc
  -- SolInstruction
  writeInstruction buf (AccountView.keyPtr sysProg) metas 2 data 12
  let rc ← sysInvokeSignedC buf infos 2 0 0
  SolanaM.require (rc == 0) rc

/-- Shared helper: write a 3-seed PDA `SolSignerSeedsC` (`[tag(4B), keySeed(32B), bump(1B)]`)
    into a 72-byte buffer `sbuf` (`seedBuf:8 + seedsArr:48 + signersArr:16`) and return `signersArr`. -/
@[inline] private def writePdaSigner3 (sbuf : Ptr) (tagU32 : UInt32) (keySeedPtr : Ptr) (bump : UInt8) :
    SolanaM Ptr := do
  let seedsArr   := sbuf + 8
  let signersArr := sbuf + 56
  storeU32 sbuf 0 tagU32
  storeU8  sbuf 4 bump
  storeU64 seedsArr 0  sbuf
  storeU64 seedsArr 8  4
  storeU64 seedsArr 16 keySeedPtr
  storeU64 seedsArr 24 32
  storeU64 seedsArr 32 (sbuf + 4)
  storeU64 seedsArr 40 1
  storeU64 signersArr 0 seedsArr
  storeU64 signersArr 8 3
  return signersArr

/-- Invoke Solana `SystemProgram::Allocate` (opcode 8u32) with a 3-seed PDA signer
    `[tag(4B), keySeed(32B), bump(1B)]` to allocate `space` bytes for `pdaAcc`.
    Combined with `systemAssignSigned` + `systemTransfer`, this creates PDA accounts on-chain
    while remaining 100% immune to pre-funding lamport griefing! -/
@[noinline] def systemAllocateSigned (sysProg pdaAcc : AccountView) (space : UInt64)
    (tagU32 : UInt32) (keySeedPtr : Ptr) (bump : UInt8) : SolanaM Unit := do
  -- 40B ix + 16B meta + 56B info + 16B data + 72B seeds = 200 bytes
  let buf ← stackAlloc 200
  let metas := buf + 40
  let infos := buf + 56
  let data  := buf + 112
  let sbuf  := buf + 128
  storeU32 data 0 8
  storeU64 data 4 space
  writeMeta metas pdaAcc 1 1
  writeAccountInfo infos pdaAcc
  writeInstruction buf (AccountView.keyPtr sysProg) metas 1 data 12
  let signersArr ← writePdaSigner3 sbuf tagU32 keySeedPtr bump
  let rc ← sysInvokeSignedC buf infos 1 signersArr 1
  SolanaM.require (rc == 0) rc

/-- Invoke Solana `SystemProgram::Assign` (opcode 1u32) with a 3-seed PDA signer
    `[tag(4B), keySeed(32B), bump(1B)]` to assign ownership of `pdaAcc` to `newOwnerKeyPtr`. -/
@[noinline] def systemAssignSigned (sysProg pdaAcc : AccountView) (newOwnerKeyPtr : Ptr)
    (tagU32 : UInt32) (keySeedPtr : Ptr) (bump : UInt8) : SolanaM Unit := do
  -- 40B ix + 16B meta + 56B info + 40B data + 72B seeds = 224 bytes
  let buf ← stackAlloc 224
  let metas := buf + 40
  let infos := buf + 56
  let data  := buf + 112
  let sbuf  := buf + 152
  storeU32 data 0 1
  pubkeyCopy (data + 4) newOwnerKeyPtr
  writeMeta metas pdaAcc 1 1
  writeAccountInfo infos pdaAcc
  writeInstruction buf (AccountView.keyPtr sysProg) metas 1 data 36
  let signersArr ← writePdaSigner3 sbuf tagU32 keySeedPtr bump
  let rc ← sysInvokeSignedC buf infos 1 signersArr 1
  SolanaM.require (rc == 0) rc

/-- Invoke SPL Token OR SPL Token-2022 `InitializeAccount3` (opcode 18u8) to initialize
    token account `account` for `mint` with owner `ownerKeyPtr` (no Rent sysvar needed!). -/
@[noinline] def tokenInitializeAccount3 (tokenProg account mint : AccountView) (ownerKeyPtr : Ptr) :
    SolanaM Unit := do
  -- 40B ix + 32B metas + 112B infos + 40B data = 224 bytes
  let buf ← stackAlloc 224
  let metas := buf + 40
  let infos := buf + 72
  let data  := buf + 184
  storeU8 data 0 18
  pubkeyCopy (data + 1) ownerKeyPtr
  writeMeta metas        account 1 0
  writeMeta (metas + 16) mint    0 0
  writeAccountInfo infos        account
  writeAccountInfo (infos + 56) mint
  writeInstruction buf (AccountView.keyPtr tokenProg) metas 2 data 33
  let rc ← sysInvokeSignedC buf infos 2 0 0
  SolanaM.require (rc == 0) rc

/-! ### Canonical Program-ID Pinning & Safe Zero-Initialization Primitives (With Formal Proofs) -/

/-- Canonical SPL Token (`TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA`) as 4 LE `UInt64` words. -/
abbrev TOKEN_PROG_W0 : UInt64 := 0x93a165d7e1f6dd06
abbrev TOKEN_PROG_W1 : UInt64 := 0xac79ebce46e1cbd9
abbrev TOKEN_PROG_W2 : UInt64 := 0x91375b5fed85b41c
abbrev TOKEN_PROG_W3 : UInt64 := 0xa900ff7e85f58c3a

/-- Canonical SPL Token-2022 (`TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb`) as 4 LE `UInt64` words. -/
abbrev TOKEN_2022_W0 : UInt64 := 0xde8f75eee1f6dd06
abbrev TOKEN_2022_W1 : UInt64 := 0xdacd6ce4bc5d4218
abbrev TOKEN_2022_W2 : UInt64 := 0x270db9834dfc1ab6
abbrev TOKEN_2022_W3 : UInt64 := 0xfc8ba1d828f9bdfe

/-- Pin `sysProg` to canonical Solana System Program (`11111111111111111111111111111111`, all 32 bytes zero). -/
@[noinline] def checkSystemProg (sysProg : AccountView) : SolanaM Unit := do
  let k := AccountView.keyPtr sysProg
  let w0 ← loadU64 k 0
  let w1 ← loadU64 k 8
  let w2 ← loadU64 k 16
  let w3 ← loadU64 k 24
  SolanaM.require ((w0 ||| w1 ||| w2 ||| w3) == 0) Err.incorrectProgramId

/-- Pin `tokProg` strictly to canonical SPL Token (`Tokenkeg...`). -/
@[noinline] def checkTokenProg (tokProg : AccountView) : SolanaM Unit := do
  let k := AccountView.keyPtr tokProg
  let w0 ← loadU64 k 0
  let w1 ← loadU64 k 8
  let w2 ← loadU64 k 16
  let w3 ← loadU64 k 24
  SolanaM.require (w0 == TOKEN_PROG_W0 && w1 == TOKEN_PROG_W1 &&
                   w2 == TOKEN_PROG_W2 && w3 == TOKEN_PROG_W3) Err.incorrectProgramId

/-- Pin `tokProg` strictly to canonical SPL Token (`Tokenkeg...`) OR SPL Token-2022 (`TokenzQd...`).
    Blocks spoofed executable program IDs (e.g., `noop.so`) from bypassing token transfers! -/
@[noinline] def checkTokenOr2022Prog (tokProg : AccountView) : SolanaM Unit := do
  let k := AccountView.keyPtr tokProg
  let w0 ← loadU64 k 0
  let w1 ← loadU64 k 8
  let w2 ← loadU64 k 16
  let w3 ← loadU64 k 24
  let isClassic := w0 == TOKEN_PROG_W0 && w1 == TOKEN_PROG_W1 &&
                   w2 == TOKEN_PROG_W2 && w3 == TOKEN_PROG_W3
  let is2022    := w0 == TOKEN_2022_W0 && w1 == TOKEN_2022_W1 &&
                   w2 == TOKEN_2022_W2 && w3 == TOKEN_2022_W3
  SolanaM.require (isClassic || is2022) Err.incorrectProgramId

/-- Zero `nWords` consecutive 8-byte words starting at `base + off`.
    Used on account initialization and closure to guarantee zero residual dirty memory! -/
@[noinline] def zeroWords (base off nWords : UInt64) : SolanaM Unit := do
  if h : nWords == 0 then return ()
  else
    storeU64 base off 0
    zeroWords base (off + 8) (nWords - 1)
termination_by nWords.toNat
decreasing_by
  have hne : nWords.toNat ≠ 0 := by
    intro hz
    have h0 : nWords = 0 := UInt64.toNat_inj.mp (by rw [hz]; rfl)
    exact h (by rw [h0]; rfl)
  have h1 : (1 : UInt64).toNat = 1 := rfl
  change (nWords - 1).toNat < nWords.toNat
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), h1]
  omega

/-! ### Formal Verification Theorems (`SvmState.mem`, 0 `sorry`, 0 custom axioms) -/

theorem checkSystemProg_sound (sysProg : AccountView) (s s' : SvmState)
    (h : checkSystemProg sysProg s = .ok () s') :
    let k := AccountView.keyPtr sysProg
    s' = s ∧
    s.readU64 (k + 0) = 0 ∧ s.readU64 (k + 8) = 0 ∧
    s.readU64 (k + 16) = 0 ∧ s.readU64 (k + 24) = 0 := by
  unfold checkSystemProg loadU64 rawLoadU64 SolanaM.require SolanaM.fail at h
  simp only [Bind.bind, SolanaM.bind] at h
  split at h
  · next hc =>
    cases h
    have hz : (s.readU64 (AccountView.keyPtr sysProg + 0) |||
               s.readU64 (AccountView.keyPtr sysProg + 8) |||
               s.readU64 (AccountView.keyPtr sysProg + 16) |||
               s.readU64 (AccountView.keyPtr sysProg + 24)) = 0 := by simpa using hc
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> bv_decide
  · cases h

theorem checkTokenProg_sound (tokProg : AccountView) (s s' : SvmState)
    (h : checkTokenProg tokProg s = .ok () s') :
    let k := AccountView.keyPtr tokProg
    s' = s ∧
    s.readU64 (k + 0) = TOKEN_PROG_W0 ∧ s.readU64 (k + 8) = TOKEN_PROG_W1 ∧
    s.readU64 (k + 16) = TOKEN_PROG_W2 ∧ s.readU64 (k + 24) = TOKEN_PROG_W3 := by
  unfold checkTokenProg loadU64 rawLoadU64 SolanaM.require SolanaM.fail at h
  simp only [Bind.bind, SolanaM.bind] at h
  split at h
  · next hc =>
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨rfl, hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩
  · cases h

theorem checkTokenOr2022Prog_sound (tokProg : AccountView) (s s' : SvmState)
    (h : checkTokenOr2022Prog tokProg s = .ok () s') :
    let k := AccountView.keyPtr tokProg
    s' = s ∧
    ((s.readU64 (k + 0) = TOKEN_PROG_W0 ∧ s.readU64 (k + 8) = TOKEN_PROG_W1 ∧
      s.readU64 (k + 16) = TOKEN_PROG_W2 ∧ s.readU64 (k + 24) = TOKEN_PROG_W3) ∨
     (s.readU64 (k + 0) = TOKEN_2022_W0 ∧ s.readU64 (k + 8) = TOKEN_2022_W1 ∧
      s.readU64 (k + 16) = TOKEN_2022_W2 ∧ s.readU64 (k + 24) = TOKEN_2022_W3)) := by
  unfold checkTokenOr2022Prog loadU64 rawLoadU64 SolanaM.require SolanaM.fail at h
  simp only [Bind.bind, SolanaM.bind] at h
  split at h
  · next hc =>
    cases h
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
    rcases hc with h1 | h2
    · exact ⟨rfl, Or.inl ⟨h1.1.1.1, h1.1.1.2, h1.1.2, h1.2⟩⟩
    · exact ⟨rfl, Or.inr ⟨h2.1.1.1, h2.1.1.2, h2.1.2, h2.2⟩⟩
  · cases h

theorem bind_ok_elim {α β : Type} {m : SolanaM α} {f : α → SolanaM β}
    {s s' : SvmState} {b : β}
    (h : (m >>= f) s = .ok b s') :
    ∃ a s0, m s = .ok a s0 ∧ f a s0 = .ok b s' := by
  cases hm : m s with
  | err c st => simp [Bind.bind, SolanaM.bind, hm] at h
  | ok a s0 => exact ⟨a, s0, rfl, by simpa [Bind.bind, SolanaM.bind, hm] using h⟩

private theorem u64_add_toNat_lt (a b : UInt64) (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]

private theorem u64_sub_toNat_le (a b : UInt64) (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  UInt64.toNat_sub_of_le a b (UInt64.le_iff_toNat_le.mpr h)

theorem mem_writeU64_outside_nat (s : SvmState) (a x v : UInt64)
    (ha : a.toNat + 8 < 2 ^ 64)
    (hd : x.toNat < a.toNat ∨ a.toNat + 8 ≤ x.toNat) :
    (s.writeU64 a v).mem x = s.mem x := by
  have hmax : (0xFFFFFFFFFFFFFFF7 : UInt64).toNat = 2 ^ 64 - 9 := by decide
  have ha' : a ≤ 0xFFFFFFFFFFFFFFF7 := UInt64.le_iff_toNat_le.mpr (by omega)
  have h8 : (8 : UInt64).toNat = 8 := rfl
  have hout : x < a ∨ a + 8 ≤ x := by
    rcases hd with h1 | h2
    · exact Or.inl (UInt64.lt_iff_toNat_lt.mpr h1)
    · exact Or.inr (UInt64.le_iff_toNat_le.mpr (by rw [u64_add_toNat_lt a 8 (by omega), h8]; omega))
  exact SvmState.mem_writeU64_outside s a x v ha' hout

theorem mem_writeU64_zero_inside (s : SvmState) (a x : UInt64)
    (_ha : a.toNat + 8 < 2 ^ 64)
    (hx1 : a.toNat ≤ x.toNat) (hx2 : x.toNat < a.toNat + 8) :
    (s.writeU64 a 0).mem x = 0 := by
  let k := x - a
  have hkLt : k < 8 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have h8 : (8 : UInt64).toNat = 8 := rfl
    show (x - a).toNat < (8 : UInt64).toNat
    rw [u64_sub_toNat_le x a hx1, h8]; omega
  have hxk : x = a + k := by show x = a + (x - a); bv_decide
  rw [hxk]
  unfold SvmState.writeU64 SvmState.writeU32 SvmState.writeU16 SvmState.writeU8
  simp only
  have e7 : (a + k == a + 4 + 2 + 1) = (k == 7) := by bv_decide
  have e6 : (a + k == a + 4 + 2)     = (k == 6) := by bv_decide
  have e5 : (a + k == a + 4 + 1)     = (k == 5) := by bv_decide
  have e4 : (a + k == a + 4)         = (k == 4) := by bv_decide
  have e3 : (a + k == a + 2 + 1)     = (k == 3) := by bv_decide
  have e2 : (a + k == a + 2)         = (k == 2) := by bv_decide
  have e1 : (a + k == a + 1)         = (k == 1) := by bv_decide
  have e0 : (a + k == a)             = (k == 0) := by bv_decide
  simp only [e7, e6, e5, e4, e3, e2, e1, e0]
  have hk8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by bv_decide
  rcases hk8 with hk | hk | hk | hk | hk | hk | hk | hk <;> (rw [hk]; rfl)

theorem readU64_of_mem_zero (s : SvmState) (a : UInt64)
    (ha : a.toNat + 8 < 2 ^ 64)
    (hz : ∀ x : UInt64, a.toNat ≤ x.toNat → x.toNat < a.toNat + 8 → s.mem x = 0) :
    s.readU64 a = 0 := by
  have hb : ∀ k : UInt64, k.toNat < 8 → s.mem (a + k) = 0 := fun k hk =>
    hz (a + k) (by rw [u64_add_toNat_lt a k (by omega)]; omega)
      (by rw [u64_add_toNat_lt a k (by omega)]; omega)
  unfold SvmState.readU64 SvmState.readU32
  have p41 : a + 4 + 1 = a + 5 := by bv_decide
  have p42 : a + 4 + 2 = a + 6 := by bv_decide
  have p43 : a + 4 + 3 = a + 7 := by bv_decide
  have p0  : a + 0 = a := by bv_decide
  have e0 := hb 0 (by decide); rw [p0] at e0
  have e1 := hb 1 (by decide)
  have e2 := hb 2 (by decide)
  have e3 := hb 3 (by decide)
  have e4 := hb 4 (by decide)
  have e5 := hb 5 (by decide)
  have e6 := hb 6 (by decide)
  have e7 := hb 7 (by decide)
  simp only [p41, p42, p43, e0, e1, e2, e3, e4, e5, e6, e7]; rfl

theorem pubkeyCopy_preserves_outside (dst src : Ptr) (s s' : SvmState)
    (hdV : dst.toNat + 32 < 2 ^ 64)
    (h : LeanSVM.pubkeyCopy dst src s = .ok () s') :
    s'.stackSp = s.stackSp ∧
    (∀ x : UInt64, x.toNat < dst.toNat ∨ dst.toNat + 32 ≤ x.toNat → s'.mem x = s.mem x) := by
  unfold LeanSVM.pubkeyCopy rawLoadU64 rawStoreU64 at h
  simp only [Bind.bind, SolanaM.bind] at h
  generalize hs1 : s.writeU64 dst (s.readU64 src) = s1 at h
  generalize hs2 : s1.writeU64 (dst + 8) (s1.readU64 (src + 8)) = s2 at h
  generalize hs3 : s2.writeU64 (dst + 16) (s2.readU64 (src + 16)) = s3 at h
  cases h
  have hsp1 : s1.stackSp = s.stackSp := by rw [← hs1]; rfl
  have hsp2 : s2.stackSp = s1.stackSp := by rw [← hs2]; rfl
  have hsp3 : s3.stackSp = s2.stackSp := by rw [← hs3]; rfl
  have h8  : (dst + 8).toNat  = dst.toNat + 8  := by have : (8 : UInt64).toNat = 8 := rfl; rw [u64_add_toNat_lt _ _ (by omega), this]
  have h16 : (dst + 16).toNat = dst.toNat + 16 := by have : (16 : UInt64).toNat = 16 := rfl; rw [u64_add_toNat_lt _ _ (by omega), this]
  have h24 : (dst + 24).toNat = dst.toNat + 24 := by have : (24 : UInt64).toNat = 24 := rfl; rw [u64_add_toNat_lt _ _ (by omega), this]
  refine ⟨by change s3.stackSp = s.stackSp; rw [hsp3, hsp2, hsp1], fun x hx => ?_⟩
  have e4 := mem_writeU64_outside_nat s3 (dst + 24) x (s3.readU64 (src + 24)) (by omega) (by omega)
  have e3 : s3.mem x = s2.mem x := by rw [← hs3]; exact mem_writeU64_outside_nat s2 (dst + 16) x (s2.readU64 (src + 16)) (by omega) (by omega)
  have e2 : s2.mem x = s1.mem x := by rw [← hs2]; exact mem_writeU64_outside_nat s1 (dst + 8) x (s1.readU64 (src + 8)) (by omega) (by omega)
  have e1 : s1.mem x = s.mem x  := by rw [← hs1]; exact mem_writeU64_outside_nat s dst x (s.readU64 src) (by omega) (by omega)
  exact e4.trans (e3.trans (e2.trans e1))

/-- Formal theorem: `zeroWords base off nWords` zeroes every single byte in
    `[base + off, base + off + nWords * 8)` from arbitrary dirty `SvmState.mem`,
    leaves all bytes outside untouched, and preserves `stackSp`. -/
theorem zeroWords_exact (base off nWords : UInt64) (s s' : SvmState)
    (hvalid : base.toNat + off.toNat + nWords.toNat * 8 < 2 ^ 64)
    (h : zeroWords base off nWords s = .ok () s') :
    s'.stackSp = s.stackSp ∧
    (∀ x : UInt64, base.toNat + off.toNat ≤ x.toNat →
      x.toNat < base.toNat + off.toNat + nWords.toNat * 8 → s'.mem x = 0) ∧
    (∀ x : UInt64, x.toNat < base.toNat + off.toNat ∨
      base.toNat + off.toNat + nWords.toNat * 8 ≤ x.toNat → s'.mem x = s.mem x) := by
  have hgen : ∀ (n : Nat) (off nWords : UInt64) (s s' : SvmState),
      nWords.toNat = n →
      base.toNat + off.toNat + nWords.toNat * 8 < 2 ^ 64 →
      zeroWords base off nWords s = .ok () s' →
      s'.stackSp = s.stackSp ∧
      (∀ x : UInt64, base.toNat + off.toNat ≤ x.toNat →
        x.toNat < base.toNat + off.toNat + nWords.toNat * 8 → s'.mem x = 0) ∧
      (∀ x : UInt64, x.toNat < base.toNat + off.toNat ∨
        base.toNat + off.toNat + nWords.toNat * 8 ≤ x.toNat → s'.mem x = s.mem x) := by
    intro n
    induction n with
    | zero =>
      intro off nWords s s' hn _ hrun
      have hz : nWords = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
      subst hz
      rw [zeroWords.eq_def] at hrun
      simp only [beq_self_eq_true, ↓reduceDIte, Pure.pure, SolanaM.pure] at hrun
      cases hrun
      exact ⟨rfl, fun _ h1 h2 => by omega, fun _ _ => rfl⟩
    | succ k ih =>
      intro off nWords s s' hn hv hrun
      have hne : (nWords == 0) = false := by
        rw [beq_eq_false_iff_ne]; intro heq; rw [heq] at hn; exact Nat.noConfusion hn
      rw [zeroWords.eq_def] at hrun
      simp only [hne, Bool.false_eq_true, ↓reduceDIte, storeU64, rawStoreU64, Bind.bind, SolanaM.bind] at hrun
      have h1nat : (1 : UInt64).toNat = 1 := rfl
      have h8nat : (8 : UInt64).toNat = 8 := rfl
      have hsub : (nWords - 1).toNat = k := by
        rw [u64_sub_toNat_le nWords 1 (by omega), h1nat, hn]; omega
      have hoff8 : (off + 8).toNat = off.toNat + 8 := by
        rw [u64_add_toNat_lt off 8 (by omega), h8nat]
      have hbo : (base + off).toNat = base.toNat + off.toNat :=
        u64_add_toNat_lt base off (by omega)
      have ⟨hsp, hzero, hout⟩ := ih (off + 8) (nWords - 1) (s.writeU64 (base + off) 0) s'
        hsub (by rw [hoff8, hsub]; omega) hrun
      refine ⟨hsp, ?_, ?_⟩
      · intro x hx1 hx2
        by_cases hlt : x.toNat < base.toNat + off.toNat + 8
        · have h1 := hout x (Or.inl (by rw [hoff8]; omega))
          rw [h1]
          exact mem_writeU64_zero_inside s (base + off) x (by rw [hbo]; omega) (by rw [hbo]; omega) (by rw [hbo]; omega)
        · exact hzero x (by rw [hoff8]; omega) (by rw [hoff8, hsub]; omega)
      · intro x hx
        have h1 := hout x (by rw [hoff8, hsub]; omega)
        rw [h1]
        exact mem_writeU64_outside_nat s (base + off) x 0 (by rw [hbo]; omega) (by rw [hbo]; omega)
  exact hgen nWords.toNat off nWords s s' rfl hvalid h

end LeanSVM.CPI
