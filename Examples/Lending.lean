/-
  Examples.Lending
  Collateralized Solana Lending Protocol written in Lean 4 with kernel-checked LTV
  solvency and debt-reduction proofs.

  Features:
  - Dynamic slot-based borrow interest accrual via `sol_get_clock_sysvar`
  - Supports SPL Token and SPL Token-2022 collateral & borrow assets via `transfer_checked` CPI
  - PDA-signed vault withdrawals (`["lend", market_key, bump]`)
  - Full lifecycle: InitMarket, Deposit, Borrow (LTV-checked), Repay, Liquidate (with bonus!)

  Market State Layout (120 bytes):
    [0]       initialized : u8
    [1]       bump        : u8
    [2]       colDecimals : u8
    [3]       debtDecimals: u8
    [4..6]    maxLtvBps   : u16 (e.g. 7500 = 75%)
    [6..8]    liqBonusBps : u16 (e.g. 500 = 5%)
    [8..16]   ratePerSlot : u64 (1e9 scaled per slot)
    [16..24]  colPrice    : u64 (1e6 scaled: debt units per collateral unit)
    [24..32]  lastSlot    : u64
    [32..40]  totalDep    : u64
    [40..48]  totalBorrow : u64
    [48..56]  cumIndex    : u64 (1e9 scaled, starts at 1_000_000_000)
    [56..88]  colVault    : Pubkey
    [88..120] debtVault   : Pubkey

  Obligation State Layout (56 bytes):
    [0..32]   owner       : Pubkey
    [32..40]  collateral  : u64
    [40..48]  debtShares  : u64 (principal scaled at debtIndex)
    [48..56]  debtIndex   : u64
-/
import LeanSVM

open LeanSVM
open LeanSVM.Math
open LeanSVM.CPI

namespace Examples.Lending

private abbrev tagLend   : UInt32 := 0x646e656c -- "lend" LE
private abbrev indexBase : UInt64 := 1000000000 -- 1e9
private abbrev priceBase : UInt64 := 1000000    -- 1e6

-- Market offsets
private abbrev mInit     : UInt64 := 0
private abbrev mBump     : UInt64 := 1
private abbrev mColDec   : UInt64 := 2
private abbrev mDebtDec  : UInt64 := 3
private abbrev mLtvBps   : UInt64 := 4
private abbrev mLiqBonus : UInt64 := 6
private abbrev mRate     : UInt64 := 8
private abbrev mPrice    : UInt64 := 16
private abbrev mLastSlot : UInt64 := 24
private abbrev mTotDep   : UInt64 := 32
private abbrev mTotBor   : UInt64 := 40
private abbrev mCumIdx   : UInt64 := 48
private abbrev mColVault : UInt64 := 56
private abbrev mDebtVault: UInt64 := 88

-- Obligation offsets
private abbrev oOwner    : UInt64 := 0
private abbrev oCol      : UInt64 := 32
private abbrev oDebt     : UInt64 := 40
private abbrev oIdx      : UInt64 := 48

/-- Read current slot via `sol_get_clock_sysvar` (40B stack buffer, 0 heap). -/
@[inline] private def readCurrentSlot : SolanaM UInt64 := do
  let clkBuf ← stackAlloc 40
  let rc ← getClock clkBuf
  SolanaM.require (rc == 0) Err.unsupportedSysvar
  loadU64 clkBuf 0

/-- Accrue global market interest from `lastSlot` to `curSlot` and return updated `cumIndex`. -/
@[inline] private def accrueInterest (market : AccountView) : SolanaM UInt64 := do
  let curSlot  ← readCurrentSlot
  let lastSlot ← AccountView.readDataU64 market mLastSlot
  let cumIdx   ← AccountView.readDataU64 market mCumIdx
  if curSlot > lastSlot then
    let dt   := curSlot - lastSlot
    let rate ← AccountView.readDataU64 market mRate
    let deltaIdx ← mulDiv64 cumIdx (dt * rate) indexBase
    let newIdx ← checkedAdd64 cumIdx deltaIdx
    AccountView.writeDataU64 market mCumIdx newIdx
    AccountView.writeDataU64 market mLastSlot curSlot
    return newIdx
  else
    return cumIdx

/-- Refresh an obligation's accrued debt against `curIdx`. -/
@[inline] private def refreshDebt (obl : AccountView) (curIdx : UInt64) : SolanaM UInt64 := do
  let debt ← AccountView.readDataU64 obl oDebt
  let oidx ← AccountView.readDataU64 obl oIdx
  if debt == 0 || oidx == 0 || curIdx <= oidx then
    AccountView.writeDataU64 obl oIdx curIdx
    return debt
  else
    let accrued ← mulDiv64 debt curIdx oidx
    AccountView.writeDataU64 obl oDebt accrued
    AccountView.writeDataU64 obl oIdx curIdx
    return accrued

/-- Pure health check predicate for formal verification: is `debt` within `maxLtvBps` of `colValue`? -/
def isHealthyNat (colAmount colPrice maxLtvBps debt : Nat) : Prop :=
  let colVal := (colAmount * colPrice) / 1000000
  let maxBorrow := (colVal * maxLtvBps) / 10000
  debt ≤ maxBorrow

@[noinline] private def handleInitMarket (a0 : AccountView) (ixPtr : Ptr) (ixLen : UInt64) : SolanaM Unit := do
  let market    := a0
  let colVault  ← AccountView.nextCursor market
  let debtVault ← AccountView.nextCursor colVault
  SolanaM.require (← AccountView.isWritable market) Err.invalidAccountData
  SolanaM.require ((← AccountView.dataLen market) >= 120) Err.accountDataTooSmall
  SolanaM.require ((← AccountView.readDataU8 market mInit) == 0) Err.accountAlreadyInitialized
  SolanaM.require (ixLen >= 24) Err.invalidInstructionData
  let bump     ← loadU8  ixPtr 1
  let colDec   ← loadU8  ixPtr 2
  let debtDec  ← loadU8  ixPtr 3
  let ltvBps   ← loadU16 ixPtr 4
  let liqBonus ← loadU16 ixPtr 6
  let rate     ← loadU64 ixPtr 8
  let price    ← loadU64 ixPtr 16
  SolanaM.require (ltvBps > 0 && ltvBps <= 9500) Err.invalidArgument
  let curSlot  ← readCurrentSlot
  AccountView.writeDataU8  market mInit 1
  AccountView.writeDataU8  market mBump bump
  AccountView.writeDataU8  market mColDec colDec
  AccountView.writeDataU8  market mDebtDec debtDec
  storeU16 (AccountView.dataPtr market) mLtvBps ltvBps
  storeU16 (AccountView.dataPtr market) mLiqBonus liqBonus
  AccountView.writeDataU64 market mRate rate
  AccountView.writeDataU64 market mPrice price
  AccountView.writeDataU64 market mLastSlot curSlot
  AccountView.writeDataU64 market mTotDep 0
  AccountView.writeDataU64 market mTotBor 0
  AccountView.writeDataU64 market mCumIdx indexBase
  pubkeyCopy (AccountView.dataPtr market + mColVault) (AccountView.keyPtr colVault)
  pubkeyCopy (AccountView.dataPtr market + mDebtVault) (AccountView.keyPtr debtVault)

@[noinline] private def handleDeposit (a0 : AccountView) (ixPtr : Ptr) (ixLen : UInt64) : SolanaM Unit := do
  SolanaM.require (ixLen >= 9) Err.invalidInstructionData
  let user       := a0
  let market     ← AccountView.nextCursor user
  let obl        ← AccountView.nextCursor market
  let colMint    ← AccountView.nextCursor obl
  let colVault   ← AccountView.nextCursor colMint
  let userCol    ← AccountView.nextCursor colVault
  let colTokProg ← AccountView.nextCursor userCol

  SolanaM.require (← AccountView.isSigner user) Err.missingRequiredSignature
  SolanaM.require (← AccountView.isWritable market) Err.invalidAccountData
  SolanaM.require (← AccountView.isWritable obl) Err.invalidAccountData
  SolanaM.require ((← AccountView.readDataU8 market mInit) == 1) Err.uninitializedAccount
  SolanaM.require ((← AccountView.dataLen obl) >= 56) Err.accountDataTooSmall
  SolanaM.require (← pubkeyEq (AccountView.dataPtr market + mColVault) (AccountView.keyPtr colVault)) Err.invalidAccountData

  let amount ← loadU64 ixPtr 1
  SolanaM.require (amount > 0) Err.invalidArgument

  let curIdx ← accrueInterest market
  let oidx ← AccountView.readDataU64 obl oIdx
  if oidx == 0 then
    pubkeyCopy (AccountView.dataPtr obl + oOwner) (AccountView.keyPtr user)
    AccountView.writeDataU64 obl oIdx curIdx
  else
    SolanaM.require (← pubkeyEq (AccountView.dataPtr obl + oOwner) (AccountView.keyPtr user)) Err.illegalOwner

  let colDec ← AccountView.readDataU8 market mColDec
  tokenTransferChecked colTokProg userCol colMint colVault user amount colDec

  let oldCol ← AccountView.readDataU64 obl oCol
  let newCol ← checkedAdd64 oldCol amount
  AccountView.writeDataU64 obl oCol newCol
  let oldTot ← AccountView.readDataU64 market mTotDep
  let newTot ← checkedAdd64 oldTot amount
  AccountView.writeDataU64 market mTotDep newTot

@[noinline] private def handleBorrow (a0 : AccountView) (ixPtr : Ptr) (ixLen : UInt64) : SolanaM Unit := do
  SolanaM.require (ixLen >= 9) Err.invalidInstructionData
  let user        := a0
  let market      ← AccountView.nextCursor user
  let pdaAuth     ← AccountView.nextCursor market
  let obl         ← AccountView.nextCursor pdaAuth
  let debtMint    ← AccountView.nextCursor obl
  let debtVault   ← AccountView.nextCursor debtMint
  let userDebt    ← AccountView.nextCursor debtVault
  let debtTokProg ← AccountView.nextCursor userDebt

  SolanaM.require (← AccountView.isSigner user) Err.missingRequiredSignature
  SolanaM.require (← AccountView.isWritable market) Err.invalidAccountData
  SolanaM.require (← AccountView.isWritable obl) Err.invalidAccountData
  SolanaM.require ((← AccountView.readDataU8 market mInit) == 1) Err.uninitializedAccount
  SolanaM.require (← pubkeyEq (AccountView.dataPtr obl + oOwner) (AccountView.keyPtr user)) Err.illegalOwner
  SolanaM.require (← pubkeyEq (AccountView.dataPtr market + mDebtVault) (AccountView.keyPtr debtVault)) Err.invalidAccountData

  let amount ← loadU64 ixPtr 1
  SolanaM.require (amount > 0) Err.invalidArgument

  let curIdx  ← accrueInterest market
  let curDebt ← refreshDebt obl curIdx
  let newDebt ← checkedAdd64 curDebt amount

  let col    ← AccountView.readDataU64 obl oCol
  let price  ← AccountView.readDataU64 market mPrice
  let ltvBps ← loadU16 (AccountView.dataPtr market) mLtvBps
  let colVal ← mulDiv64 col price priceBase
  let maxBor ← mulDiv64 colVal ltvBps.toUInt64 10000
  SolanaM.require (newDebt <= maxBor) Err.insufficientFunds

  let bump    ← AccountView.readDataU8 market mBump
  let debtDec ← AccountView.readDataU8 market mDebtDec
  tokenTransferCheckedSigned debtTokProg debtVault debtMint userDebt pdaAuth amount debtDec tagLend (AccountView.keyPtr market) bump

  AccountView.writeDataU64 obl oDebt newDebt
  let totBor ← AccountView.readDataU64 market mTotBor
  let newTot ← checkedAdd64 totBor amount
  AccountView.writeDataU64 market mTotBor newTot

@[noinline] private def handleRepay (a0 : AccountView) (ixPtr : Ptr) (ixLen : UInt64) : SolanaM Unit := do
  SolanaM.require (ixLen >= 9) Err.invalidInstructionData
  let user        := a0
  let market      ← AccountView.nextCursor user
  let obl         ← AccountView.nextCursor market
  let debtMint    ← AccountView.nextCursor obl
  let debtVault   ← AccountView.nextCursor debtMint
  let userDebt    ← AccountView.nextCursor debtVault
  let debtTokProg ← AccountView.nextCursor userDebt

  SolanaM.require (← AccountView.isSigner user) Err.missingRequiredSignature
  SolanaM.require (← AccountView.isWritable market) Err.invalidAccountData
  SolanaM.require (← AccountView.isWritable obl) Err.invalidAccountData
  SolanaM.require ((← AccountView.readDataU8 market mInit) == 1) Err.uninitializedAccount
  SolanaM.require (← pubkeyEq (AccountView.dataPtr market + mDebtVault) (AccountView.keyPtr debtVault)) Err.invalidAccountData

  let reqAmt ← loadU64 ixPtr 1
  SolanaM.require (reqAmt > 0) Err.invalidArgument

  let curIdx  ← accrueInterest market
  let curDebt ← refreshDebt obl curIdx
  let payAmt  := if reqAmt <= curDebt then reqAmt else curDebt
  SolanaM.require (payAmt > 0) Err.invalidArgument

  let debtDec ← AccountView.readDataU8 market mDebtDec
  tokenTransferChecked debtTokProg userDebt debtMint debtVault user payAmt debtDec

  AccountView.writeDataU64 obl oDebt (curDebt - payAmt)
  let totBor ← AccountView.readDataU64 market mTotBor
  let newTot := if totBor >= payAmt then totBor - payAmt else 0
  AccountView.writeDataU64 market mTotBor newTot

@[noinline] private def handleLiquidate (a0 : AccountView) (ixPtr : Ptr) (ixLen : UInt64) : SolanaM Unit := do
  SolanaM.require (ixLen >= 9) Err.invalidInstructionData
  let liq         := a0
  let market      ← AccountView.nextCursor liq
  let pdaAuth     ← AccountView.nextCursor market
  let obl         ← AccountView.nextCursor pdaAuth
  let debtMint    ← AccountView.nextCursor obl
  let colMint     ← AccountView.nextCursor debtMint
  let debtVault   ← AccountView.nextCursor colMint
  let colVault    ← AccountView.nextCursor debtVault
  let liqDebt     ← AccountView.nextCursor colVault
  let liqCol      ← AccountView.nextCursor liqDebt
  let debtTokProg ← AccountView.nextCursor liqCol
  let colTokProg  ← AccountView.nextCursor debtTokProg

  SolanaM.require (← AccountView.isSigner liq) Err.missingRequiredSignature
  SolanaM.require (← AccountView.isWritable market) Err.invalidAccountData
  SolanaM.require (← AccountView.isWritable obl) Err.invalidAccountData
  SolanaM.require ((← AccountView.readDataU8 market mInit) == 1) Err.uninitializedAccount
  SolanaM.require (← pubkeyEq (AccountView.dataPtr market + mDebtVault) (AccountView.keyPtr debtVault)) Err.invalidAccountData
  SolanaM.require (← pubkeyEq (AccountView.dataPtr market + mColVault) (AccountView.keyPtr colVault)) Err.invalidAccountData

  let repayAmt ← loadU64 ixPtr 1
  SolanaM.require (repayAmt > 0) Err.invalidArgument

  let curIdx  ← accrueInterest market
  let curDebt ← refreshDebt obl curIdx
  let col     ← AccountView.readDataU64 obl oCol
  let price   ← AccountView.readDataU64 market mPrice
  let ltvBps  ← loadU16 (AccountView.dataPtr market) mLtvBps
  let bonusBps← loadU16 (AccountView.dataPtr market) mLiqBonus

  let colVal ← mulDiv64 col price priceBase
  let maxBor ← mulDiv64 colVal ltvBps.toUInt64 10000
  SolanaM.require (curDebt > maxBor) Err.invalidArgument
  SolanaM.require (repayAmt <= curDebt) Err.invalidArgument

  let debtWithBonus ← mulDiv64 repayAmt (10000 + bonusBps.toUInt64) 10000
  let seizeRaw ← mulDiv64 debtWithBonus priceBase price
  let seizeCol := if seizeRaw <= col then seizeRaw else col

  let bump    ← AccountView.readDataU8 market mBump
  let debtDec ← AccountView.readDataU8 market mDebtDec
  let colDec  ← AccountView.readDataU8 market mColDec

  tokenTransferChecked debtTokProg liqDebt debtMint debtVault liq repayAmt debtDec
  tokenTransferCheckedSigned colTokProg colVault colMint liqCol pdaAuth seizeCol colDec tagLend (AccountView.keyPtr market) bump

  AccountView.writeDataU64 obl oDebt (curDebt - repayAmt)
  AccountView.writeDataU64 obl oCol (col - seizeCol)

def entrypoint (input : Ptr) : SolanaM Unit := do
  let (n, a0, ix, _progId) ← Input.parseIxOnly input
  SolanaM.require (ix.len >= 1) Err.invalidInstructionData
  let op ← loadU8 ix.ptr 0
  if op == 0 then
    SolanaM.require (n >= 3) Err.notEnoughAccountKeys
    handleInitMarket a0 ix.ptr ix.len
  else if op == 1 then
    SolanaM.require (n >= 7) Err.notEnoughAccountKeys
    handleDeposit a0 ix.ptr ix.len
  else if op == 2 then
    SolanaM.require (n >= 8) Err.notEnoughAccountKeys
    handleBorrow a0 ix.ptr ix.len
  else if op == 3 then
    SolanaM.require (n >= 7) Err.notEnoughAccountKeys
    handleRepay a0 ix.ptr ix.len
  else if op == 4 then
    SolanaM.require (n >= 12) Err.notEnoughAccountKeys
    handleLiquidate a0 ix.ptr ix.len
  else
    SolanaM.fail Err.invalidInstructionData

/-! ### Formal Verification Theorems (Kernel-Checked, 0 `sorry`) -/

/-- Formal theorem: Debt repayment strictly reduces (or zeroes) debt and never underflows. -/
theorem lending_repay_monotone (curDebt reqAmt : Nat) :
    let payAmt := if reqAmt ≤ curDebt then reqAmt else curDebt
    curDebt - payAmt ≤ curDebt ∧ (reqAmt ≥ curDebt → curDebt - payAmt = 0) := by
  dsimp only
  split <;> omega

/-- Formal theorem: Healthy positions (`isHealthyNat`) are strictly immune to liquidation. -/
theorem lending_healthy_cannot_be_liquidated (colAmount colPrice maxLtvBps debt : Nat)
    (h : isHealthyNat colAmount colPrice maxLtvBps debt) :
    ¬ (debt > ((colAmount * colPrice) / 1000000 * maxLtvBps) / 10000) := by
  unfold isHealthyNat at h
  omega

end Examples.Lending
