/-
  Examples.CompilerRegression
  End-to-end LiteSVM regression & microbenchmark exercising:
  1. Exact Solana sBPF `ALU32` sign-extension fixup (`add32`/`sub32`/`mul32` crossing bit 31)
  2. `VRange` interval analysis (`add32`/`mul32` -> `add64`/`mul64` promotion, redundant low-bit
     mask elimination, and range-proven dead-branch folding)
  3. Constant-length `sol_memset_` inline expansion (`0x00`, `0xFF`, and arbitrary byte `0xAB`
     with zero `sol_memset_` syscall overhead!)
  4. Interprocedural dead-helper elimination (`removeDeadHelpers`)

  Accounts:
    0. `[writable]` Output buffer account (128 bytes, owned by this program)
       - `[0..8]`   : `(a + b).toUInt64` where `a, b : UInt32` from `ix[0..8]`
       - `[8..16]`  : `(c - d).toUInt64` where `c, d : UInt32` from `ix[8..16]`
       - `[16..24]` : `(e * f).toUInt64` where `e, f : UInt32` from `ix[16..24]`
       - `[24..32]` : range-promoted `((u8_0.toUInt32 + u8_1.toUInt32).toUInt64 &&& 0xFF) + ...`
       - `[32..72]` : 40 bytes filled with `0x00` via inline `memset` (5 x `stdw 0`)
       - `[72..104]`: 32 bytes filled with `0xFF` via inline `memset` (4 x `stdw -1`)
       - `[104..124]`: 20 bytes filled with `0xAB` via inline `memset` (5 x `stw 0xABABABAB`)
       - `[124..128]`: untouched sentinel bytes (must remain `0x55`)
-/
import LeanSVM

open LeanSVM

namespace Examples.CompilerRegression

/-- Unreachable helper that MUST be stripped by `removeDeadHelpers` after `VRange` folds the
    impossible `u8 > 500` branch! -/
@[noinline] def unreachableHelper (acc : AccountView) (v : UInt64) : SolanaM Unit := do
  AccountView.writeDataU64 acc 0 (v + 1)
  AccountView.writeDataU64 acc 8 (v + 2)
  AccountView.writeDataU64 acc 16 (v + 3)
  AccountView.writeDataU64 acc 24 (v + 4)

def entrypoint (input : Ptr) : SolanaM Unit := do
  let (outAcc, ix, progId) ← Input.parse1 input
  let writable ← AccountView.isWritable outAcc
  SolanaM.require writable Err.invalidAccountData
  let owned ← pubkeyEq (AccountView.ownerPtr outAcc) progId
  SolanaM.require owned Err.illegalOwner
  let dlen ← AccountView.dataLen outAcc
  SolanaM.require (dlen == 224) Err.invalidAccountData
  SolanaM.require (ix.len == 42) Err.invalidInstructionData

  -- 1. Sign-extension edge cases on UInt32 arithmetic (crossing bit 31!)
  let a ← loadU32 ix.ptr 0
  let b ← loadU32 ix.ptr 4
  let c ← loadU32 ix.ptr 8
  let d ← loadU32 ix.ptr 12
  let e ← loadU32 ix.ptr 16
  let f ← loadU32 ix.ptr 20

  let sum32 : UInt32 := a + b
  let dif32 : UInt32 := c - d
  let mul32 : UInt32 := e * f

  AccountView.writeDataU64 outAcc 0 sum32.toUInt64
  AccountView.writeDataU64 outAcc 8 dif32.toUInt64
  AccountView.writeDataU64 outAcc 16 mul32.toUInt64

  -- 2. VRange optimizations:
  --    - `u0, u1 ∈ [0, 255]` so `u0.toUInt32 + u1.toUInt32` promotes `add32 -> add64`
  --    - `u0.toUInt64 &&& 0xFF` eliminates the redundant mask
  --    - `u0.toUInt64 > 500` folds to `false`, making `unreachableHelper` dead!
  let u0 ← loadU8 ix.ptr 24
  let u1 ← loadU8 ix.ptr 25
  if u0.toUInt64 > 500 then
    unreachableHelper outAcc u0.toUInt64
  else
    let prom : UInt32 := u0.toUInt32 + u1.toUInt32
    let masked : UInt64 := u0.toUInt64 &&& 0xFF
    AccountView.writeDataU64 outAcc 24 (prom.toUInt64 + masked)

    -- 3. Constant-length `sol_memset_` inline expansion (0x00, 0xFF, 0xAB)
    let base := AccountView.dataPtr outAcc
    memset (base + 32)  0x00 40
    memset (base + 72)  0xFF 32
    memset (base + 104) 0xAB 20

    -- 4. Total Lean scalar semantics (`Nat.sub` saturation, `UInt64`/`UInt32` div/mod by 0, shift32 >= 32)
    --    Stored into `[32..64]` (overwriting first 32B of the zeroed region for verification)
    let natSeed ← loadU64 ix.ptr 26
    let div64In ← loadU64 ix.ptr 34
    let natSat : UInt64 := (natSeed.toNat - 1).toUInt64
    let q64 := (1000 : UInt64) / div64In
    let r64 := (1000 : UInt64) % div64In
    let div32In : UInt32 := div64In.toUInt32
    let q32 : UInt32 := (1000 : UInt32) / div32In
    let r32 : UInt32 := (1000 : UInt32) % div32In
    let sh32 : UInt32 := (3 : UInt32) <<< (33 : UInt32)  -- masks 33 % 32 = 1 -> 6
    AccountView.writeDataU64 outAcc 32 natSat
    AccountView.writeDataU64 outAcc 40 (q64 ^^^ r64)
    AccountView.writeDataU64 outAcc 48 ((q32 ^^^ r32).toUInt64)
    AccountView.writeDataU64 outAcc 56 sh32.toUInt64

    -- 5. Positive LiteSVM check for `sol_memcmp_` (equal & late-byte signed i32 diff) + full 40B `sol_get_clock_sysvar`!
    let cmpBufA ← stackAlloc 32
    let cmpBufB ← stackAlloc 32
    let cmpRes  ← stackAlloc 8
    memset cmpBufA 0xFF 32
    memset cmpBufB 0xFF 32
    sysMemcmp cmpBufA cmpBufB 32 cmpRes
    let eqRes ← loadU32 cmpRes 0
    storeU8 cmpBufA 31 5
    storeU8 cmpBufB 31 8
    sysMemcmp cmpBufA cmpBufB 32 cmpRes
    let diffRes ← loadU32 cmpRes 0  -- 5 - 8 = -3 = 0xFFFFFFFD (signed i32!)
    AccountView.writeDataU64 outAcc 128 eqRes.toUInt64
    AccountView.writeDataU64 outAcc 136 diffRes.toUInt64
    let clockBuf ← stackAlloc 40
    let rcClk ← getClock clockBuf  -- writes all 40B (5 x u64) to stack buffer (Agave forbids MM_INPUT_START!)
    SolanaM.require (rcClk == 0) Err.unsupportedSysvar
    AccountView.writeDataU64 outAcc 144 (← loadU64 clockBuf 0)
    AccountView.writeDataU64 outAcc 152 (← loadU64 clockBuf 8)
    AccountView.writeDataU64 outAcc 160 (← loadU64 clockBuf 16)
    AccountView.writeDataU64 outAcc 168 (← loadU64 clockBuf 24)
    AccountView.writeDataU64 outAcc 176 (← loadU64 clockBuf 32)
    -- 6. Multi-slice `sol_sha256(["ab", "c"])` differential check against `LeanSVM.Sha256.nist_abc`!
    let shaSlices ← stackAlloc 32
    let shaData   ← stackAlloc 8
    storeU8 shaData 0 0x61 -- 'a'
    storeU8 shaData 1 0x62 -- 'b'
    storeU8 shaData 4 0x63 -- 'c'
    storeU64 shaSlices 0  shaData
    storeU64 shaSlices 8  2
    storeU64 shaSlices 16 (shaData + 4)
    storeU64 shaSlices 24 1
    let rcSha ← sha256 shaSlices 2 (base + 184)
    SolanaM.require (rcSha == 0) Err.invalidArgument

end Examples.CompilerRegression
