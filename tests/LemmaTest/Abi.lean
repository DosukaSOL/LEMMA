/-
  LemmaTest.Abi — serialize a Solana program input buffer (ABI v1, the loader's "aligned" format)
  so compiled programs can be run in the interpreter with realistic account layouts.

  Non-duplicate entry: 0xFF, is_signer, is_writable, executable, 4 pad bytes, key[32], owner[32],
  lamports u64, data_len u64, data, 10240 bytes realloc padding, pad to 8, rent_epoch u64.
  Duplicate entry: index of the original slot (u8), 7 pad bytes.
  Then: instruction data length u64, instruction data, program id[32].
-/
import LemmaTest.Harness

namespace LemmaTest.Abi
open LemmaTest

def key32 (seed : UInt8) : ByteArray := ⟨(List.range 32).toArray.map fun i => seed + i.toUInt8⟩

structure Account where
  key : ByteArray
  owner : ByteArray
  lamports : UInt64 := 1_000_000
  data : ByteArray := .empty
  signer : Bool := false
  writable : Bool := false
  executable : Bool := false

inductive Slot where
  | acct (a : Account)
  | dup (index : UInt8)

def zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩
def b (x : Bool) : UInt8 := if x then 1 else 0

/-- Returns the buffer and the byte offset of each slot (for reading account data back). -/
def serialize (slots : List Slot) (ix : ByteArray) (programId : ByteArray) : ByteArray × Array Nat :=
  Id.run do
    let mut buf := u64le slots.length.toUInt64
    let mut offs := #[]
    for s in slots do
      offs := offs.push buf.size
      match s with
      | .dup i => buf := buf.push i ++ zeros 7
      | .acct a =>
        buf := buf.push 0xFF |>.push (b a.signer) |>.push (b a.writable) |>.push (b a.executable)
        buf := buf ++ zeros 4 ++ a.key ++ a.owner ++ u64le a.lamports ++ u64le a.data.size.toUInt64
        buf := buf ++ a.data ++ zeros 10240
        let pad := (8 - buf.size % 8) % 8
        buf := buf ++ zeros pad ++ u64le 0
    buf := buf ++ u64le ix.size.toUInt64 ++ ix ++ programId
    return (buf, offs)

/-- Data bytes of the account at slot offset `off` (data starts 88 bytes into the entry). -/
def dataAt (buf : ByteArray) (off : Nat) (len : Nat) : ByteArray := buf.extract (off + 88) (off + 88 + len)

end LemmaTest.Abi
