/-
  Examples.HashCheck
  Zero-heap Solana program demonstrating:
  - sBPF stack buffer allocation (`stackAlloc`, 0 bytes of heap!)
  - `sol_sha256` syscall (hashes arbitrary instruction data bytes)
  - `sol_get_clock_sysvar` syscall (reads on-chain Clock slot)
  - `sol_log_` syscall (string literal in `.rodata`)

  Accounts:
    0. `[writable]` State account (>= 40 bytes: `[0..32]` = sha256(ix_data), `[32..40]` = slot u64)
-/
import LeanSVM

open LeanSVM

namespace Examples.HashCheck

def entrypoint (input : Ptr) : SolanaM Unit := do
  let (stateAcc, ix, _progId) ← Input.parse1 input
  let writable ← AccountView.isWritable stateAcc
  SolanaM.require writable Err.invalidAccountData
  let dlen ← AccountView.dataLen stateAcc
  SolanaM.require (dlen >= 40) Err.accountDataTooSmall

  -- Allocate a 16-byte SolBytes slice descriptor `(ptr, len)` directly on the sBPF stack (0 heap!)
  let sliceDesc ← stackAlloc 16
  storeU64 sliceDesc 0 ix.ptr
  storeU64 sliceDesc 8 ix.len

  -- Hash `ix` directly into `stateAcc.data[0..32]` via `sol_sha256` (zero intermediate copy!)
  let rc ← sha256 sliceDesc 1 (AccountView.dataPtr stateAcc)
  SolanaM.require (rc == 0) Err.invalidArgument

  -- Allocate 40-byte Clock sysvar buffer on stack, read Clock, store `slot` at `stateAcc.data[32..40]`
  let clockBuf ← stackAlloc 40
  let crc ← getClock clockBuf
  SolanaM.require (crc == 0) Err.unsupportedSysvar
  let slot ← loadU64 clockBuf 0
  AccountView.writeDataU64 stateAcc 32 slot

  log "lean-svm: sha256+clock ok"

end Examples.HashCheck
