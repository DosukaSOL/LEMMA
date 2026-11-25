/-
  LeanSVM.Types
  Zero-copy Solana SVM primitive types, error codes, and ABI constants.
  Every type here unboxes into a single 64-bit sBPF register (or two registers for Slice).
-/

namespace LeanSVM

/-- Raw 64-bit SVM virtual address (unboxed to a single sBPF register). -/
abbrev Ptr := UInt64

/- Standard Solana ProgramError codes encoded in `r0` (0 = success). -/
namespace Err
  abbrev success                  : UInt64 := 0
  abbrev customBase               : UInt64 := 0x0000000100000000 -- fallback if needed
  abbrev invalidArgument          : UInt64 := 0x0000000200000000
  abbrev invalidInstructionData   : UInt64 := 0x0000000300000000
  abbrev invalidAccountData       : UInt64 := 0x0000000400000000
  abbrev accountDataTooSmall      : UInt64 := 0x0000000500000000
  abbrev insufficientFunds        : UInt64 := 0x0000000600000000
  abbrev incorrectProgramId       : UInt64 := 0x0000000700000000
  abbrev missingRequiredSignature : UInt64 := 0x0000000800000000
  abbrev accountAlreadyInitialized: UInt64 := 0x0000000900000000
  abbrev uninitializedAccount     : UInt64 := 0x0000000a00000000
  abbrev notEnoughAccountKeys     : UInt64 := 0x0000000b00000000
  abbrev accountBorrowFailed      : UInt64 := 0x0000000c00000000
  abbrev maxSeedLengthExceeded    : UInt64 := 0x0000000d00000000
  abbrev invalidSeeds             : UInt64 := 0x0000000e00000000
  abbrev borshIoError             : UInt64 := 0x0000000f00000000
  abbrev accountNotRentExempt     : UInt64 := 0x0000001000000000
  abbrev unsupportedSysvar        : UInt64 := 0x0000001100000000
  abbrev illegalOwner             : UInt64 := 0x0000001200000000
  abbrev maxAccountsDataAlloc     : UInt64 := 0x0000001300000000
  abbrev invalidRealloc           : UInt64 := 0x0000001400000000
  abbrev arithmeticOverflow       : UInt64 := 0x0000001800000000

  /-- Custom program error code `c` (non-zero `UInt32`, encoded in lower 32 bits of `r0`). -/
  @[inline] def custom (code : UInt32) : UInt64 := code.toUInt64
end Err

/- Exact Solana SVM ABI v1 serialized input buffer layout offsets. -/
namespace ABI
  abbrev nonDupMarker             : UInt8  := 0xFF
  abbrev accDupOffset             : UInt64 := 0
  abbrev accIsSignerOffset        : UInt64 := 1
  abbrev accIsWritableOffset      : UInt64 := 2
  abbrev accIsExecutableOffset    : UInt64 := 3
  abbrev accOrigDataLenOffset     : UInt64 := 4
  abbrev accKeyOffset             : UInt64 := 8
  abbrev accOwnerOffset           : UInt64 := 40
  abbrev accLamportsOffset        : UInt64 := 72
  abbrev accDataLenOffset         : UInt64 := 80
  abbrev accDataOffset            : UInt64 := 88
  abbrev maxPermittedDataIncrease : UInt64 := 10240
  /-- Total fixed bytes after account header: 88 (hdr) + 10240 (realloc) + 8 (rent_epoch) = 10336. -/
  abbrev accFixedStride           : UInt64 := 10336
  /-- `((data_len + 10336 + 7) & ~7)` = `(data_len + 10343) & 0xFFFFFFFFFFFFFFF8`. -/
  abbrev accStrideRoundAdd        : UInt64 := 10343
  abbrev align8Mask               : UInt64 := 0xFFFFFFFFFFFFFFF8
  abbrev pubkeySize               : UInt64 := 32
end ABI

/-- Zero-copy handle to an account inside the SVM serialized input buffer.
    Compiled directly to a single 64-bit register holding the account's base address. -/
abbrev AccountView := Ptr

/-- Zero-copy byte slice `(ptr, len)` scalarized into two 64-bit registers. -/
structure ByteSlice where
  ptr : Ptr
  len : UInt64
  deriving Repr, BEq

end LeanSVM
