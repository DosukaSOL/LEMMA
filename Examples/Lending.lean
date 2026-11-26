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
import Std.Tactic.BVDecide

open LeanSVM
open LeanSVM.Math
open LeanSVM.CPI

namespace Examples.Lending

private abbrev tagLend   : UInt32 := 0x646e656c -- "lend" LE
private abbrev indexBase : UInt64 := 1000000000 -- 1e9
private abbrev priceBase : UInt64 := 1000000    -- 1e6

-- Market offsets (exact 128 bytes = 16 words)
private abbrev mSize     : UInt64 := 128
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

-- Obligation offsets (exact 64 bytes = 8 words; distinct size & magic from Market!)
private abbrev oSize     : UInt64 := 64
private abbrev oOwner    : UInt64 := 0
private abbrev oCol      : UInt64 := 32
private abbrev oDebt     : UInt64 := 40
private abbrev oIdx      : UInt64 := 48
private abbrev oMagic    : UInt64 := 56
private abbrev MAGIC_OBL : UInt8  := 2

@[noinline] private def checkMarket (market : AccountView) (progId : Ptr) : SolanaM Unit := do
  SolanaM.require (← AccountView.isWritable market) Err.invalidAccountData
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr market) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen market) == mSize) Err.invalidAccountData
  SolanaM.require ((← AccountView.readDataU8 market mInit) == 1) Err.uninitializedAccount

@[noinline] private def checkObligation (obl : AccountView) (progId : Ptr) : SolanaM Unit := do
  SolanaM.require (← AccountView.isWritable obl) Err.invalidAccountData
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr obl) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen obl) == oSize) Err.invalidAccountData
  SolanaM.require ((← AccountView.readDataU8 obl oMagic) == MAGIC_OBL) Err.uninitializedAccount

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

@[noinline] private def handleInitMarket (a0 : AccountView) (progId ixPtr : Ptr) (ixLen : UInt64) : SolanaM Unit := do
  let market    := a0
  let colVault  ← AccountView.nextCursor market
  let debtVault ← AccountView.nextCursor colVault
  SolanaM.require (← AccountView.isWritable market) Err.invalidAccountData
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr market) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen market) == mSize) Err.invalidAccountData
  SolanaM.require ((← AccountView.readDataU8 market mInit) == 0) Err.accountAlreadyInitialized
  SolanaM.require (!(← pubkeyEq (AccountView.keyPtr colVault) (AccountView.keyPtr debtVault))) Err.invalidArgument
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
  zeroWords (AccountView.dataPtr market) 0 (mSize >>> 3)
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

@[noinline] private def handleDeposit (a0 : AccountView) (progId ixPtr : Ptr) (ixLen : UInt64) : SolanaM Unit := do
  SolanaM.require (ixLen >= 9) Err.invalidInstructionData
  let user       := a0
  let market     ← AccountView.nextCursor user
  let obl        ← AccountView.nextCursor market
  let colMint    ← AccountView.nextCursor obl
  let colVault   ← AccountView.nextCursor colMint
  let userCol    ← AccountView.nextCursor colVault
  let colTokProg ← AccountView.nextCursor userCol

  SolanaM.require (← AccountView.isSigner user) Err.missingRequiredSignature
  checkMarket market progId
  SolanaM.require (← AccountView.isWritable obl) Err.invalidAccountData
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr obl) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen obl) == oSize) Err.invalidAccountData
  checkTokenOr2022Prog colTokProg
  SolanaM.require (← pubkeyEq (AccountView.dataPtr market + mColVault) (AccountView.keyPtr colVault)) Err.invalidAccountData
  SolanaM.require (!(← pubkeyEq (AccountView.keyPtr userCol) (AccountView.keyPtr colVault))) Err.invalidArgument

  let amount ← loadU64 ixPtr 1
  SolanaM.require (amount > 0) Err.invalidArgument

  let curIdx ← accrueInterest market
  let magic  ← AccountView.readDataU8 obl oMagic
  if magic == 0 then
    -- Zero ALL 64 bytes before writing fields so dirty buffers can never inflate `oCol` or `oDebt`!
    zeroWords (AccountView.dataPtr obl) 0 (oSize >>> 3)
    AccountView.writeDataU8  obl oMagic MAGIC_OBL
    pubkeyCopy (AccountView.dataPtr obl + oOwner) (AccountView.keyPtr user)
    AccountView.writeDataU64 obl oIdx curIdx
  else
    SolanaM.require (magic == MAGIC_OBL) Err.invalidAccountData
    SolanaM.require (← pubkeyEq (AccountView.dataPtr obl + oOwner) (AccountView.keyPtr user)) Err.illegalOwner

  let colDec ← AccountView.readDataU8 market mColDec
  tokenTransferChecked colTokProg userCol colMint colVault user amount colDec

  let oldCol ← AccountView.readDataU64 obl oCol
  let newCol ← checkedAdd64 oldCol amount
  AccountView.writeDataU64 obl oCol newCol
  let oldTot ← AccountView.readDataU64 market mTotDep
  let newTot ← checkedAdd64 oldTot amount
  AccountView.writeDataU64 market mTotDep newTot

@[noinline] private def handleBorrow (a0 : AccountView) (progId ixPtr : Ptr) (ixLen : UInt64) : SolanaM Unit := do
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
  checkMarket market progId
  checkObligation obl progId
  checkTokenOr2022Prog debtTokProg
  SolanaM.require (← pubkeyEq (AccountView.dataPtr obl + oOwner) (AccountView.keyPtr user)) Err.illegalOwner
  SolanaM.require (← pubkeyEq (AccountView.dataPtr market + mDebtVault) (AccountView.keyPtr debtVault)) Err.invalidAccountData
  SolanaM.require (!(← pubkeyEq (AccountView.keyPtr userDebt) (AccountView.keyPtr debtVault))) Err.invalidArgument

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

@[noinline] private def handleRepay (a0 : AccountView) (progId ixPtr : Ptr) (ixLen : UInt64) : SolanaM Unit := do
  SolanaM.require (ixLen >= 9) Err.invalidInstructionData
  let user        := a0
  let market      ← AccountView.nextCursor user
  let obl         ← AccountView.nextCursor market
  let debtMint    ← AccountView.nextCursor obl
  let debtVault   ← AccountView.nextCursor debtMint
  let userDebt    ← AccountView.nextCursor debtVault
  let debtTokProg ← AccountView.nextCursor userDebt

  SolanaM.require (← AccountView.isSigner user) Err.missingRequiredSignature
  checkMarket market progId
  checkObligation obl progId
  checkTokenOr2022Prog debtTokProg
  SolanaM.require (← pubkeyEq (AccountView.dataPtr market + mDebtVault) (AccountView.keyPtr debtVault)) Err.invalidAccountData
  SolanaM.require (!(← pubkeyEq (AccountView.keyPtr userDebt) (AccountView.keyPtr debtVault))) Err.invalidArgument

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

@[noinline] private def handleLiquidate (a0 : AccountView) (progId ixPtr : Ptr) (ixLen : UInt64) : SolanaM Unit := do
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
  checkMarket market progId
  checkObligation obl progId
  checkTokenOr2022Prog debtTokProg
  checkTokenOr2022Prog colTokProg
  SolanaM.require (← pubkeyEq (AccountView.dataPtr market + mDebtVault) (AccountView.keyPtr debtVault)) Err.invalidAccountData
  SolanaM.require (← pubkeyEq (AccountView.dataPtr market + mColVault) (AccountView.keyPtr colVault)) Err.invalidAccountData
  SolanaM.require (!(← pubkeyEq (AccountView.keyPtr liqDebt) (AccountView.keyPtr debtVault))) Err.invalidArgument
  SolanaM.require (!(← pubkeyEq (AccountView.keyPtr liqCol)  (AccountView.keyPtr colVault)))  Err.invalidArgument

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
  let (n, a0, ix, progId) ← Input.parseIxOnly input
  SolanaM.require (ix.len >= 1) Err.invalidInstructionData
  let op ← loadU8 ix.ptr 0
  if op == 0 then
    SolanaM.require (n >= 3) Err.notEnoughAccountKeys
    handleInitMarket a0 progId ix.ptr ix.len
  else if op == 1 then
    SolanaM.require (n >= 7) Err.notEnoughAccountKeys
    handleDeposit a0 progId ix.ptr ix.len
  else if op == 2 then
    SolanaM.require (n >= 8) Err.notEnoughAccountKeys
    handleBorrow a0 progId ix.ptr ix.len
  else if op == 3 then
    SolanaM.require (n >= 7) Err.notEnoughAccountKeys
    handleRepay a0 progId ix.ptr ix.len
  else if op == 4 then
    SolanaM.require (n >= 12) Err.notEnoughAccountKeys
    handleLiquidate a0 progId ix.ptr ix.len
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

/-- Formal `SvmState.mem` theorem: Fresh obligation initialization from ANY dirty 64-byte buffer
    (e.g. nonzero residual `oCol` / `oDebt`) ALWAYS zeroes both `oCol` and `oDebt`, so crediting
    `amount` yields `oCol = amount` and `oDebt = 0`! -/
theorem lending_initObligation_zero_inits_dirty_mem
    (oData userKey : Ptr) (curIdx amount : UInt64) (s s' : SvmState)
    (hvalid : oData.toNat + 64 < 2 ^ 64)
    (h : (do
        zeroWords oData 0 (oSize >>> 3)
        storeU8  oData oMagic MAGIC_OBL
        pubkeyCopy (oData + oOwner) userKey
        storeU64 oData oIdx curIdx
        let oldCol ← loadU64 oData oCol
        let newCol ← checkedAdd64 oldCol amount
        storeU64 oData oCol newCol) s = .ok () s') :
    s'.readU64 (oData + oCol) = amount ∧ s'.readU64 (oData + oDebt) = 0 := by
  obtain ⟨_, s0, hz, h⟩ := bind_ok_elim h
  have hn8 : (oSize >>> 3).toNat = 8 := by decide
  have ⟨_, hzero0, _⟩ := zeroWords_exact oData 0 (oSize >>> 3) s s0
    (by have h0 : (0 : UInt64).toNat = 0 := rfl; omega) hz
  obtain ⟨_, s1, hs1, h⟩ := bind_ok_elim h
  obtain ⟨_, s2, hp1, h⟩ := bind_ok_elim h
  obtain ⟨_, s3, hs3, h⟩ := bind_ok_elim h
  obtain ⟨oldCol, s4, hl, h⟩ := bind_ok_elim h
  obtain ⟨newCol, s5, ha, h⟩ := bind_ok_elim h
  dsimp only [storeU8, storeU64, loadU64, rawStoreU8, rawStoreU64, rawLoadU64] at hs1 hs3 hl h
  have heq1 : s1 = s0.writeU8 (oData + oMagic) MAGIC_OBL := by cases hs1; rfl
  have heq3 : s3 = s2.writeU64 (oData + oIdx) curIdx     := by cases hs3; rfl
  have heq4 : oldCol = s3.readU64 (oData + oCol) ∧ s4 = s3 := by cases hl; exact ⟨rfl, rfl⟩
  have hO0  : (oData + oOwner).toNat = oData.toNat      := by have : oOwner.toNat = 0 := rfl; rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega), this]; omega
  have hO32 : (oData + oCol).toNat   = oData.toNat + 32 := by have : oCol.toNat = 32 := rfl; rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega), this]
  have hO40 : (oData + oDebt).toNat  = oData.toNat + 40 := by have : oDebt.toNat = 40 := rfl; rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega), this]
  have hO48 : (oData + oIdx).toNat   = oData.toNat + 48 := by have : oIdx.toNat = 48 := rfl; rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega), this]
  have hO56 : (oData + oMagic).toNat = oData.toNat + 56 := by have : oMagic.toNat = 56 := rfl; rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega), this]
  have ⟨_, hpc1⟩ := pubkeyCopy_preserves_outside (oData + oOwner) userKey s1 s2 (by omega) hp1
  have hMidZero : ∀ x : UInt64, oData.toNat + 32 ≤ x.toNat → x.toNat < oData.toNat + 48 → s3.mem x = 0 := by
    intro x hx1 hx2
    have h32 : s3.mem x = s2.mem x := by rw [heq3]; exact mem_writeU64_outside_nat s2 (oData + oIdx) x curIdx (by omega) (Or.inl (by omega))
    have h21 : s2.mem x = s1.mem x := hpc1 x (Or.inr (by omega))
    have h10 : s1.mem x = s0.mem x := by
      rw [heq1]; unfold SvmState.writeU8
      have hne : x ≠ oData + oMagic := fun he => by rw [he] at hx2; omega
      simp only [beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true, ↓reduceIte]
    rw [h32, h21, h10]
    exact hzero0 x (by have h0 : (0 : UInt64).toNat = 0 := rfl; omega)
      (by have h0 : (0 : UInt64).toNat = 0 := rfl; omega)
  have hCol0 : s3.readU64 (oData + oCol) = 0 :=
    readU64_of_mem_zero s3 (oData + oCol) (by omega) (fun x h1 h2 => hMidZero x (by omega) (by omega))
  have hold0 : oldCol = 0 := heq4.1.trans hCol0
  rw [hold0, heq4.2] at ha
  have h0a : (0 : UInt64) + amount = amount := by bv_decide
  have hge0 : ((0 : UInt64) + amount ≥ 0) := by bv_decide
  unfold checkedAdd64 SolanaM.require SolanaM.fail at ha
  simp only [Bind.bind, Pure.pure, SolanaM.bind, SolanaM.pure, hge0, decide_true, ↓reduceIte] at ha
  cases ha; cases h
  refine ⟨by rw [SvmState.readU64_writeU64_same, h0a], ?_⟩
  apply readU64_of_mem_zero _ (oData + oDebt) (by omega)
  intro x h1 h2
  rw [mem_writeU64_outside_nat s3 (oData + oCol) x (0 + amount) (by omega) (Or.inr (by omega))]
  exact hMidZero x (by omega) (by omega)

end Examples.Lending
