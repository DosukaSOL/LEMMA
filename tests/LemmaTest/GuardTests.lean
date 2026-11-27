/-
  LemmaTest.GuardTests — attack tests for the account-validation layer, run against the COMPILED
  `Lemma.Examples.GuardedCounter` program in the interpreter. Each attack must be rejected with
  the expected error code and must leave the counter unchanged.
-/
import LemmaTest.Abi
import Lemma.Examples.GuardedCounter

namespace LemmaTest.GuardTests
open Lean LemmaTest LemmaTest.Abi

def PROGRAM := key32 0xA0
def AUTH := key32 0x10
def OTHER := key32 0x30
def TAG : UInt64 := 0x52544E554F434D4C

def counterData (tag : UInt64) (auth : ByteArray) (count : UInt64) : ByteArray :=
  u64le tag ++ auth ++ u64le count

def authAcct : Account := { key := AUTH, owner := key32 0x00, signer := true }
def counterAcct (count : UInt64) : Account :=
  { key := key32 0x50, owner := PROGRAM, writable := true, data := counterData TAG AUTH count }

def ERR_SIG : UInt64 := 0x0000000800000000
def ERR_ACCOUNT_DATA : UInt64 := 0x0000000400000000
def ERR_OWNER : UInt64 := 0x0000001200000000
def ERR_OVERFLOW : UInt64 := 0x0000001800000000
def ERR_DUP : UInt64 := 0x4C4D0002
def ERR_KIND : UInt64 := 0x4C4D0003
def ERR_NOT_ENOUGH : UInt64 := 0x0000000B00000000

/-- Run one scenario on BOTH the compiled binary (interpreter) and the Lean definition the
    theorems are about; check the expected outcome and that the two agree. -/
def scenario (prog : Compiled) (name : String) (slots : List Slot) (want : Sbpf.Halt)
    (wantCount? : Option UInt64) : TestM Unit := do
  let (input, offs) := serialize slots .empty PROGRAM
  let (halt, st) := prog.run input
  check (halt == want) fun _ => s!"{name}: want {repr want}, got {repr halt}"
  -- model side: evaluate the Lean entrypoint itself
  let (code, s') := LeanSVM.SolanaM.runEntry
    (Lemma.Examples.GuardedCounter.entrypoint Sbpf.inputStart) (leanState input)
  check (Sbpf.Halt.exit code == halt) fun _ =>
    s!"{name}: Lean model returned {code}, compiled binary {repr halt}"
  if let some wantCount := wantCount? then
    let after := st.inputBytes input.size
    let cnt := readU64le (dataAt after (offs[1]!) 48) 40
    check (cnt == wantCount) fun _ => s!"{name}: counter is {cnt}, expected {wantCount}"
    let cntModel := s'.readU64 (Sbpf.inputStart + (offs[1]! + 88 + 40).toUInt64)
    check (cntModel == cnt) fun _ => s!"{name}: Lean model counter {cntModel} ≠ binary {cnt}"
  IO.println s!"   {if halt == want then "✓" else "✗"} {name}"

def suite (env : Environment) : TestM Unit := do
  section_ "Account-validation attacks: compiled GuardedCounter vs its Lean definition"
  match compile env `Lemma.Examples.GuardedCounter.entrypoint with
  | .error e => check false fun _ => s!"GuardedCounter: compile error {e}"
  | .ok prog =>
    let c := counterAcct 41
    scenario prog "honest increment (41 → 42)" [.acct authAcct, .acct c] (.exit 0) (some 42)
    scenario prog "missing signer" [.acct { authAcct with signer := false }, .acct c]
      (.exit ERR_SIG) (some 41)
    scenario prog "counter passed read-only" [.acct authAcct, .acct { c with writable := false }]
      (.exit ERR_ACCOUNT_DATA) (some 41)
    scenario prog "counter owned by another program (spoofed account)"
      [.acct authAcct, .acct { c with owner := OTHER }] (.exit ERR_OWNER) (some 41)
    scenario prog "wrong account kind (type confusion)"
      [.acct authAcct, .acct { c with data := counterData (TAG + 1) AUTH 41 }] (.exit ERR_KIND) (some 41)
    scenario prog "uninitialized (zeroed) counter"
      [.acct authAcct, .acct { c with data := zeros 48 }] (.exit ERR_KIND) none
    scenario prog "data too short for a tag" [.acct authAcct, .acct { c with data := zeros 4 }]
      (.exit ERR_KIND) none
    scenario prog "wrong data length" [.acct authAcct, .acct { c with data := c.data ++ zeros 8 }]
      (.exit ERR_ACCOUNT_DATA) (some 41)
    scenario prog "signer is not the stored authority"
      [.acct { authAcct with key := OTHER }, .acct c] (.exit ERR_OWNER) (some 41)
    scenario prog "authority passed twice (duplicate slot as counter)"
      [.acct authAcct, .dup 0] (.exit ERR_DUP) none
    scenario prog "counter overflow (u64::MAX)" [.acct authAcct, .acct (counterAcct 0xFFFFFFFFFFFFFFFF)]
      (.exit ERR_OVERFLOW) (some 0xFFFFFFFFFFFFFFFF)
    scenario prog "too few accounts" [.acct authAcct] (.exit ERR_NOT_ENOUGH) none

end LemmaTest.GuardTests
