/-
  Lemma.Components.FeeSplitter — split lamports from a program-owned vault to three fixed
  recipients by basis-point shares. The shares always sum EXACTLY to the requested amount.
  The rounding dust goes to recipient 0, and the theorem bounds it to less than 2 lamports.

  Accounts (both instructions):
    0. authority  [signer]
    1. vault      [writable], owned by this program
    2. recipient0, 3. recipient1, 4. recipient2   ([writable] for `Split`)

  Vault data (168 bytes):
    [0,8) kind tag `TAG` (0 = uninitialized) · [8,40) authority key
    [40,48) bps0 · [48,56) bps1 · [56,64) bps2   (u64 each, summing to 10000)
    [64,96) recipient0 key · [96,128) recipient1 key · [128,160) recipient2 key
    [160,168) reserve: lamports the vault must keep (e.g. its rent-exempt minimum)

  Instruction data: byte 0 = opcode.
    0 `Init`  : bps0, bps1, bps2, reserve (u64 LE at offsets 1, 9, 17, 25)
    1 `Split` : amount (u64 LE at offset 1)

  `Split` moves `amount` out of the vault: recipient1 gets ⌊amount·bps1/10000⌋, recipient2 gets
  ⌊amount·bps2/10000⌋, and recipient0 gets the rest, which is its own floor share plus the
  dust. No CPI is involved: a program may debit lamports from accounts it owns, and the runtime
  allows crediting any writable account.
-/
import LeanSVM
import Lemma.Guard
import Lemma.Parse
import Lemma.Math.MulDiv

namespace Lemma.LErr
open LeanSVM
/-- A recipient account is not the one recorded in the splitter configuration. -/
abbrev wrongRecipient : UInt64 := Err.custom 0x4C4D0004
end Lemma.LErr

namespace Lemma.Components.FeeSplitter
open LeanSVM Lemma.Guard Lemma.Spec Lemma.Math

/-- Account-kind tag: ASCII "LMSPLIT1" as a little-endian `u64`. -/
abbrev TAG : UInt64 := 0x3154494C50534D4C
abbrev DATA_LEN : UInt64 := 168
abbrev BPS : UInt64 := 10000

/-- Byte offsets of the configuration fields, relative to the account slot (data starts at +88). -/
abbrev offTag : UInt64 := 88
abbrev offAuth : UInt64 := 88 + 8
abbrev offBps0 : UInt64 := 88 + 40
abbrev offBps1 : UInt64 := 88 + 48
abbrev offBps2 : UInt64 := 88 + 56
abbrev offR0 : UInt64 := 88 + 64
abbrev offR1 : UInt64 := 88 + 96
abbrev offR2 : UInt64 := 88 + 128
abbrev offReserve : UInt64 := 88 + 160
/-- Offset of the lamport balance in an account slot. -/
abbrev offLamports : UInt64 := 72

@[inline] def validBps (b0 b1 b2 : UInt64) : Bool :=
  b0 ≤ BPS && b1 ≤ BPS && b2 ≤ BPS && b0 + b1 + b2 == BPS

/-- Copy a 32-byte key (4 words). -/
@[inline] def copyKey (dst src : Ptr) : SolanaM Unit :=
  SolanaM.bind (rawLoadU64 src) fun w0 => SolanaM.bind (rawLoadU64 (src + 8)) fun w1 =>
  SolanaM.bind (rawLoadU64 (src + 16)) fun w2 => SolanaM.bind (rawLoadU64 (src + 24)) fun w3 =>
  SolanaM.bind (rawStoreU64 dst w0) fun _ => SolanaM.bind (rawStoreU64 (dst + 8) w1) fun _ =>
  SolanaM.bind (rawStoreU64 (dst + 16) w2) fun _ => rawStoreU64 (dst + 24) w3

/-- Everything `Init` writes except the kind tag (which is written last, by `initIx`). -/
@[inline] def initWrites (auth vault r0 r1 r2 : AccountView) (b0 b1 b2 reserve : UInt64) :
    SolanaM Unit := do
  copyKey (vault + offAuth) (AccountView.keyPtr auth)
  copyKey (vault + offR0) (AccountView.keyPtr r0)
  copyKey (vault + offR1) (AccountView.keyPtr r1)
  copyKey (vault + offR2) (AccountView.keyPtr r2)
  rawStoreU64 (vault + offBps0) b0
  rawStoreU64 (vault + offBps1) b1
  rawStoreU64 (vault + offBps2) b2
  rawStoreU64 (vault + offReserve) reserve

def initIx (auth vault r0 r1 r2 : AccountView) (ixPtr ixLen : UInt64) (progId : Ptr) : SolanaM Unit := do
  requireNonDup auth
  requireNonDup vault
  requireNonDup r0
  requireNonDup r1
  requireNonDup r2
  requireSigner auth
  requireWritable vault
  requireOwner vault progId
  let len ← rawLoadU64 (vault + 80)
  SolanaM.require (len == DATA_LEN) Err.invalidAccountData
  let tag ← rawLoadU64 (vault + offTag)
  SolanaM.require (tag == 0) Err.accountAlreadyInitialized
  SolanaM.require (ixLen ≥ 33) Err.invalidInstructionData
  let b0 ← rawLoadU64 (ixPtr + 1)
  let b1 ← rawLoadU64 (ixPtr + 9)
  let b2 ← rawLoadU64 (ixPtr + 17)
  let reserve ← rawLoadU64 (ixPtr + 25)
  SolanaM.require (validBps b0 b1 b2) Err.invalidInstructionData
  let bal ← rawLoadU64 (vault + offLamports)
  SolanaM.require (bal ≥ reserve) Err.insufficientFunds
  initWrites auth vault r0 r1 r2 b0 b1 b2 reserve
  rawStoreU64 (vault + offTag) TAG

def splitIx (auth vault r0 r1 r2 : AccountView) (ixPtr ixLen : UInt64) (progId : Ptr) : SolanaM Unit := do
  requireNonDup auth
  requireNonDup vault
  requireNonDup r0
  requireNonDup r1
  requireNonDup r2
  requireSigner auth
  requireWritable vault
  requireWritable r0
  requireWritable r1
  requireWritable r2
  requireOwner vault progId
  requireTag vault TAG
  requireKey auth (vault + offAuth) Err.illegalOwner
  requireKey r0 (vault + offR0) LErr.wrongRecipient
  requireKey r1 (vault + offR1) LErr.wrongRecipient
  requireKey r2 (vault + offR2) LErr.wrongRecipient
  requireDisjoint (vault + offLamports) (r0 + offLamports)
  requireDisjoint (vault + offLamports) (r1 + offLamports)
  requireDisjoint (vault + offLamports) (r2 + offLamports)
  requireDisjoint (r0 + offLamports) (r1 + offLamports)
  requireDisjoint (r0 + offLamports) (r2 + offLamports)
  requireDisjoint (r1 + offLamports) (r2 + offLamports)
  let len ← rawLoadU64 (vault + 80)
  SolanaM.require (len == DATA_LEN) Err.invalidAccountData
  SolanaM.require (ixLen ≥ 9) Err.invalidInstructionData
  let amount ← rawLoadU64 (ixPtr + 1)
  let b0 ← rawLoadU64 (vault + offBps0)
  let b1 ← rawLoadU64 (vault + offBps1)
  let b2 ← rawLoadU64 (vault + offBps2)
  let reserve ← rawLoadU64 (vault + offReserve)
  SolanaM.require (validBps b0 b1 b2) Err.invalidAccountData
  let s1 ← mulDivFloorM amount b1 BPS
  let s2 ← mulDivFloorM amount b2 BPS
  let s12 ← checkedAdd64 s1 s2
  let s0 ← checkedSub64 amount s12
  let bv ← rawLoadU64 (vault + offLamports)
  let bl0 ← rawLoadU64 (r0 + offLamports)
  let bl1 ← rawLoadU64 (r1 + offLamports)
  let bl2 ← rawLoadU64 (r2 + offLamports)
  let bvNew ← checkedSub64 bv amount Err.insufficientFunds
  SolanaM.require (bvNew ≥ reserve) Err.insufficientFunds
  let n0 ← checkedAdd64 bl0 s0
  let n1 ← checkedAdd64 bl1 s1
  let n2 ← checkedAdd64 bl2 s2
  rawStoreU64 (vault + offLamports) bvNew
  rawStoreU64 (r0 + offLamports) n0
  rawStoreU64 (r1 + offLamports) n1
  rawStoreU64 (r2 + offLamports) n2

def entrypoint (input : Ptr) : SolanaM Unit := do
  let (auth, vault, r0, r1, r2, ix, progId) ← Input.parse5 input
  SolanaM.require (ix.len ≥ 1) Err.invalidInstructionData
  let op ← rawLoadU8 ix.ptr
  if op == 0 then initIx auth vault r0 r1 r2 ix.ptr ix.len progId
  else if op == 1 then splitIx auth vault r0 r1 r2 ix.ptr ix.len progId
  else SolanaM.fail Err.invalidInstructionData

end Lemma.Components.FeeSplitter
