/-
  Examples.DutchAuction
  On-chain Solana NFT Dutch Auction written in Lean 4 with kernel-checked price-bound
  and monotonic-decay theorems!

  Features:
  - Linear declining price from `startPrice` to `reservePrice` over `[startSlot, endSlot]`
    driven by live Solana `Clock.slot` (`sol_get_clock_sysvar`)
  - Supports both SPL Token and SPL Token-2022 NFTs (1-of-1 `amount = 1, decimals = 0`)
  - PDA-controlled NFT escrow vault (`["auct", auction_key, bump]`)
  - Atomic SOL payment via `SystemProgram::Transfer` CPI + PDA-signed NFT delivery!

  Auction Account Layout (144 bytes):
    [0]        status       : u8  (0=Uninit, 1=Active, 2=Settled, 3=Cancelled)
    [1]        bump         : u8
    [2]        nftDecimals  : u8
    [8..40]    seller       : Pubkey
    [40..72]   nftMint      : Pubkey
    [72..104]  escrowVault  : Pubkey
    [104..112] startPrice   : u64 (lamports)
    [112..120] reservePrice : u64 (lamports)
    [120..128] startSlot    : u64
    [128..136] endSlot      : u64
    [136..144] settledPrice : u64
-/
import LeanSVM

open LeanSVM
open LeanSVM.Math
open LeanSVM.CPI

namespace Examples.DutchAuction

private abbrev tagAuct : UInt32 := 0x74637561 -- "auct" LE

private abbrev aStatus   : UInt64 := 0
private abbrev aBump     : UInt64 := 1
private abbrev aDec      : UInt64 := 2
private abbrev aSeller   : UInt64 := 8
private abbrev aMint     : UInt64 := 40
private abbrev aEscrow   : UInt64 := 72
private abbrev aStartP   : UInt64 := 104
private abbrev aReserveP : UInt64 := 112
private abbrev aStartS   : UInt64 := 120
private abbrev aEndS     : UInt64 := 128
private abbrev aSettledP : UInt64 := 136

/-- Pure mathematical Dutch auction price decay function (used in formal proofs). -/
def dutchPriceNat (startP reserveP startS endS curS : Nat) : Nat :=
  if curS ≤ startS then startP
  else if curS ≥ endS then reserveP
  else
    let elapsed := curS - startS
    let duration := endS - startS
    let drop := ((startP - reserveP) * elapsed) / duration
    startP - drop

/-- Runtime overflow-safe 128-bit Dutch price computation. -/
@[inline] private def computeDutchPrice (startP reserveP startS endS curS : UInt64) : SolanaM UInt64 := do
  if curS <= startS then
    return startP
  else if curS >= endS then
    return reserveP
  else
    let elapsed  := curS - startS
    let duration := endS - startS
    let spread   := startP - reserveP
    let drop     ← mulDiv64 spread elapsed duration
    return startP - drop

@[inline] private def readSlot : SolanaM UInt64 := do
  let buf ← stackAlloc 40
  let rc ← getClock buf
  SolanaM.require (rc == 0) Err.unsupportedSysvar
  loadU64 buf 0

@[noinline] private def handleCreate (a0 : AccountView) (ixPtr : Ptr) (ixLen : UInt64) : SolanaM Unit := do
  SolanaM.require (ixLen >= 35) Err.invalidInstructionData
  let seller    := a0
  let auction   ← AccountView.nextCursor seller
  let nftMint   ← AccountView.nextCursor auction
  let sellerNft ← AccountView.nextCursor nftMint
  let escrow    ← AccountView.nextCursor sellerNft
  let tokProg   ← AccountView.nextCursor escrow

  SolanaM.require (← AccountView.isSigner seller) Err.missingRequiredSignature
  SolanaM.require (← AccountView.isWritable auction) Err.invalidAccountData
  SolanaM.require ((← AccountView.dataLen auction) >= 144) Err.accountDataTooSmall
  SolanaM.require ((← AccountView.readDataU8 auction aStatus) == 0) Err.accountAlreadyInitialized

  let bump     ← loadU8  ixPtr 1
  let dec      ← loadU8  ixPtr 2
  let startP   ← loadU64 ixPtr 3
  let reserveP ← loadU64 ixPtr 11
  let startS   ← loadU64 ixPtr 19
  let endS     ← loadU64 ixPtr 27
  SolanaM.require (startP >= reserveP && endS > startS) Err.invalidArgument

  tokenTransferChecked tokProg sellerNft nftMint escrow seller 1 dec

  AccountView.writeDataU8  auction aStatus 1
  AccountView.writeDataU8  auction aBump bump
  AccountView.writeDataU8  auction aDec dec
  pubkeyCopy (AccountView.dataPtr auction + aSeller) (AccountView.keyPtr seller)
  pubkeyCopy (AccountView.dataPtr auction + aMint)   (AccountView.keyPtr nftMint)
  pubkeyCopy (AccountView.dataPtr auction + aEscrow) (AccountView.keyPtr escrow)
  AccountView.writeDataU64 auction aStartP startP
  AccountView.writeDataU64 auction aReserveP reserveP
  AccountView.writeDataU64 auction aStartS startS
  AccountView.writeDataU64 auction aEndS endS
  AccountView.writeDataU64 auction aSettledP 0

@[noinline] private def handleBuy (a0 : AccountView) (ixPtr : Ptr) (ixLen : UInt64) : SolanaM Unit := do
  SolanaM.require (ixLen >= 9) Err.invalidInstructionData
  let buyer    := a0
  let seller   ← AccountView.nextCursor buyer
  let auction  ← AccountView.nextCursor seller
  let pdaAuth  ← AccountView.nextCursor auction
  let nftMint  ← AccountView.nextCursor pdaAuth
  let escrow   ← AccountView.nextCursor nftMint
  let buyerNft ← AccountView.nextCursor escrow
  let tokProg  ← AccountView.nextCursor buyerNft
  let sysProg  ← AccountView.nextCursor tokProg

  SolanaM.require (← AccountView.isSigner buyer) Err.missingRequiredSignature
  SolanaM.require (← AccountView.isWritable auction) Err.invalidAccountData
  SolanaM.require ((← AccountView.readDataU8 auction aStatus) == 1) Err.invalidAccountData
  SolanaM.require (← pubkeyEq (AccountView.dataPtr auction + aSeller) (AccountView.keyPtr seller)) Err.illegalOwner
  SolanaM.require (← pubkeyEq (AccountView.dataPtr auction + aMint)   (AccountView.keyPtr nftMint)) Err.invalidAccountData
  SolanaM.require (← pubkeyEq (AccountView.dataPtr auction + aEscrow) (AccountView.keyPtr escrow)) Err.invalidAccountData

  let maxPrice ← loadU64 ixPtr 1
  let startP   ← AccountView.readDataU64 auction aStartP
  let reserveP ← AccountView.readDataU64 auction aReserveP
  let startS   ← AccountView.readDataU64 auction aStartS
  let endS     ← AccountView.readDataU64 auction aEndS
  let curSlot  ← readSlot

  let price ← computeDutchPrice startP reserveP startS endS curSlot
  SolanaM.require (price <= maxPrice) Err.invalidArgument

  systemTransfer sysProg buyer seller price
  let bump ← AccountView.readDataU8 auction aBump
  let dec  ← AccountView.readDataU8 auction aDec
  tokenTransferCheckedSigned tokProg escrow nftMint buyerNft pdaAuth 1 dec tagAuct (AccountView.keyPtr auction) bump

  AccountView.writeDataU8  auction aStatus 2
  AccountView.writeDataU64 auction aSettledP price

@[noinline] private def handleCancel (a0 : AccountView) : SolanaM Unit := do
  let seller    := a0
  let auction   ← AccountView.nextCursor seller
  let pdaAuth   ← AccountView.nextCursor auction
  let nftMint   ← AccountView.nextCursor pdaAuth
  let escrow    ← AccountView.nextCursor nftMint
  let sellerNft ← AccountView.nextCursor escrow
  let tokProg   ← AccountView.nextCursor sellerNft

  SolanaM.require (← AccountView.isSigner seller) Err.missingRequiredSignature
  SolanaM.require (← AccountView.isWritable auction) Err.invalidAccountData
  SolanaM.require ((← AccountView.readDataU8 auction aStatus) == 1) Err.invalidAccountData
  SolanaM.require (← pubkeyEq (AccountView.dataPtr auction + aSeller) (AccountView.keyPtr seller)) Err.illegalOwner
  SolanaM.require (← pubkeyEq (AccountView.dataPtr auction + aEscrow) (AccountView.keyPtr escrow)) Err.invalidAccountData

  let bump ← AccountView.readDataU8 auction aBump
  let dec  ← AccountView.readDataU8 auction aDec
  tokenTransferCheckedSigned tokProg escrow nftMint sellerNft pdaAuth 1 dec tagAuct (AccountView.keyPtr auction) bump
  AccountView.writeDataU8 auction aStatus 3

def entrypoint (input : Ptr) : SolanaM Unit := do
  let (n, a0, ix, _progId) ← Input.parseIxOnly input
  SolanaM.require (ix.len >= 1) Err.invalidInstructionData
  let op ← loadU8 ix.ptr 0
  if op == 0 then
    SolanaM.require (n >= 6) Err.notEnoughAccountKeys
    handleCreate a0 ix.ptr ix.len
  else if op == 1 then
    SolanaM.require (n >= 9) Err.notEnoughAccountKeys
    handleBuy a0 ix.ptr ix.len
  else if op == 2 then
    SolanaM.require (n >= 7) Err.notEnoughAccountKeys
    handleCancel a0
  else
    SolanaM.fail Err.invalidInstructionData

/-! ### Formal Verification Theorems (Kernel-Checked, 0 `sorry`) -/

/-- Formal theorem: Dutch auction price is ALWAYS bounded within `[reservePrice, startPrice]`. -/
theorem dutchPrice_bounded (startP reserveP startS endS curS : Nat)
    (hp : reserveP ≤ startP) (hs : startS < endS) :
    reserveP ≤ dutchPriceNat startP reserveP startS endS curS ∧
    dutchPriceNat startP reserveP startS endS curS ≤ startP := by
  unfold dutchPriceNat
  split
  · omega
  · split
    · omega
    · dsimp only
      have hel : curS - startS ≤ endS - startS := by omega
      have hdrop : ((startP - reserveP) * (curS - startS)) / (endS - startS) ≤ startP - reserveP := by
        apply Nat.div_le_of_le_mul
        have h1 := Nat.mul_le_mul_left (startP - reserveP) hel
        simpa [Nat.mul_comm] using h1
      exact ⟨by omega, Nat.sub_le _ _⟩

/-- Formal theorem: Dutch auction price is monotonically non-increasing in slot (`s1 ≤ s2 → price s2 ≤ price s1`). -/
theorem dutchPrice_monotone (startP reserveP startS endS s1 s2 : Nat)
    (hp : reserveP ≤ startP) (hs : startS < endS) (hle : s1 ≤ s2) :
    dutchPriceNat startP reserveP startS endS s2 ≤ dutchPriceNat startP reserveP startS endS s1 := by
  have hb1 := dutchPrice_bounded startP reserveP startS endS s1 hp hs
  unfold dutchPriceNat
  split
  · have h1 : s1 ≤ startS := by omega
    simp [h1]
  · split
    · simpa [dutchPriceNat] using hb1.1
    · split
      · dsimp only; exact Nat.sub_le _ _
      · split
        · omega
        · dsimp only
          have hmul : (startP - reserveP) * (s1 - startS) ≤ (startP - reserveP) * (s2 - startS) :=
            Nat.mul_le_mul_left (startP - reserveP) (by omega)
          have hdiv : ((startP - reserveP) * (s1 - startS)) / (endS - startS) ≤
                      ((startP - reserveP) * (s2 - startS)) / (endS - startS) :=
            Nat.div_le_div_right hmul
          exact Nat.sub_le_sub_left hdiv startP

end Examples.DutchAuction
