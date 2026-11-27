/-
  LemmaTest.FeeSplitterTests — the compiled fee splitter vs its Lean definition (the code the
  theorems are about), on honest flows, attacks, and a randomized split differential. In every
  scenario the binary and the Lean model must agree on the result code AND on every balance.
-/
import LemmaTest.Abi
import Lemma.Components.FeeSplitter

namespace LemmaTest.FeeSplitterTests
open Lean LemmaTest LemmaTest.Abi

def PROGRAM := key32 0xA0
def AUTH := key32 0x10
def MALLORY := key32 0x30
def R0 := key32 0x60
def R1 := key32 0x70
def R2 := key32 0x80
def VAULT := key32 0x50
def TAG : UInt64 := 0x3154494C50534D4C

def ERR_SIG : UInt64 := 0x0000000800000000
def ERR_ACCOUNT_DATA : UInt64 := 0x0000000400000000
def ERR_OWNER : UInt64 := 0x0000001200000000
def ERR_IX : UInt64 := 0x0000000300000000
def ERR_FUNDS : UInt64 := 0x0000000600000000
def ERR_ALREADY_INIT : UInt64 := 0x0000000900000000
def ERR_DUP : UInt64 := 0x4C4D0002
def ERR_KIND : UInt64 := 0x4C4D0003
def ERR_RECIPIENT : UInt64 := 0x4C4D0004

def cfgData (b0 b1 b2 reserve : UInt64) (auth r0 r1 r2 : ByteArray) : ByteArray :=
  u64le TAG ++ auth ++ u64le b0 ++ u64le b1 ++ u64le b2 ++ r0 ++ r1 ++ r2 ++ u64le reserve

def initIx (b0 b1 b2 reserve : UInt64) : ByteArray :=
  (ByteArray.mk #[0]) ++ u64le b0 ++ u64le b1 ++ u64le b2 ++ u64le reserve
def splitIx (amount : UInt64) : ByteArray := (ByteArray.mk #[1]) ++ u64le amount

def authA : Account := { key := AUTH, owner := key32 0, signer := true }
def vaultA (lamports : UInt64) (data : ByteArray) : Account :=
  { key := VAULT, owner := PROGRAM, writable := true, lamports, data }
def rcpt (k : ByteArray) (lamports : UInt64 := 1_000) : Account := { key := k, owner := key32 0, writable := true, lamports }

structure Outcome where
  code : UInt64
  lamports : Array UInt64
  after : ByteArray
  offs : Array Nat

/-- Run on both the binary and the Lean model; check they agree; return the binary's outcome. -/
def runBoth (prog : Compiled) (name : String) (slots : List Slot) (ix : ByteArray) :
    TestM (Option Outcome) := do
  let (input, offs) := serialize slots ix PROGRAM
  let (halt, st) := prog.run input
  let (code, s') := LeanSVM.SolanaM.runEntry
    (Lemma.Components.FeeSplitter.entrypoint Sbpf.inputStart) (leanState input)
  let after := st.inputBytes input.size
  let binLam := offs.map fun o => readU64le after (o + 72)
  let modelLam := offs.map fun o => s'.readU64 (Sbpf.inputStart + (o + 72).toUInt64)
  match halt with
  | .exit c =>
    check (c == code) fun _ => s!"{name}: binary exit {c} but Lean model {code}"
    check (binLam == modelLam) fun _ => s!"{name}: balances differ, binary {binLam} vs model {modelLam}"
    -- every byte of the input region (all account data, flags, balances) must agree
    let modelBytes : ByteArray :=
      ⟨(List.range input.size).toArray.map fun i => s'.readU8 (Sbpf.inputStart + i.toUInt64)⟩
    check (after.data == modelBytes.data) fun _ => s!"{name}: memory differs between binary and model"
    return some { code := c, lamports := binLam, after, offs }
  | other =>
    check false fun _ => s!"{name}: binary halted abnormally: {repr other}"
    return none

def expect (prog : Compiled) (name : String) (slots : List Slot) (ix : ByteArray) (wantCode : UInt64)
    (wantLam? : Option (Array UInt64) := none) : TestM Unit := do
  if let some o ← runBoth prog name slots ix then
    check (o.code == wantCode) fun _ => s!"{name}: exit {o.code}, expected {wantCode}"
    if let some w := wantLam? then
      check (o.lamports == w) fun _ => s!"{name}: balances {o.lamports}, expected {w}"
    IO.println s!"   {if o.code == wantCode then "✓" else "✗"} {name}"

def suite (env : Environment) : TestM Unit := do
  section_ "FeeSplitter: compiled binary vs Lean definition (honest flows, attacks, differential)"
  match compile env `Lemma.Components.FeeSplitter.entrypoint with
  | .error e => check false fun _ => s!"FeeSplitter compile error: {e}"
  | .ok prog =>
    let cfg := cfgData 3333 3333 3334 500 AUTH R0 R1 R2
    let ok := [Slot.acct authA, .acct (vaultA 1_000_000 cfg), .acct (rcpt R0), .acct (rcpt R1), .acct (rcpt R2)]
    -- Init
    let fresh := vaultA 1_000_000 (zeros 168)
    let initSlots := [Slot.acct authA, .acct fresh, .acct (rcpt R0), .acct (rcpt R1), .acct (rcpt R2)]
    expect prog "init: honest" initSlots (initIx 3333 3333 3334 500) 0
    if let some o ← runBoth prog "init: writes exactly the configuration" initSlots (initIx 3333 3333 3334 500) then
      check (dataAt o.after o.offs[1]! 168 == cfg) fun _ => "init: vault data is not the expected configuration"
    expect prog "init: re-initialization rejected" ok (initIx 3333 3333 3334 500) ERR_ALREADY_INIT
    expect prog "init: shares not summing to 10000" initSlots (initIx 3333 3333 3333 500) ERR_IX
    expect prog "init: share > 10000 (overflow trick 2^64-…)" initSlots
      (initIx 0xFFFFFFFFFFFFD8F0 10000 10000 500) ERR_IX
    expect prog "init: authority did not sign" (.acct { authA with signer := false } :: initSlots.drop 1)
      (initIx 3333 3333 3334 500) ERR_SIG
    expect prog "init: reserve above vault balance" initSlots (initIx 3333 3333 3334 2_000_000) ERR_FUNDS
    expect prog "init: vault owned by another program"
      [.acct authA, .acct { fresh with owner := MALLORY }, .acct (rcpt R0), .acct (rcpt R1), .acct (rcpt R2)]
      (initIx 3333 3333 3334 500) ERR_OWNER
    -- Split: 1001 lamports at 33.33/33.33/33.34 % → 333, 333, and 335 (= 333 floor + 2 dust)
    expect prog "split: honest 1001 → r0 335 (incl. 2 dust), r1 333, r2 333" ok (splitIx 1001) 0
      (some #[1_000_000, 1_000_000 - 1001, 1_000 + 335, 1_000 + 333, 1_000 + 333])
    expect prog "split: zero amount is a no-op" ok (splitIx 0) 0
      (some #[1_000_000, 1_000_000, 1_000, 1_000, 1_000])
    expect prog "split: would breach the reserve" ok (splitIx 999_501) ERR_FUNDS
    expect prog "split: more than the vault holds" ok (splitIx 2_000_000) ERR_FUNDS
    expect prog "split: wrong recipient (attacker's account)"
      [.acct authA, .acct (vaultA 1_000_000 cfg), .acct (rcpt MALLORY), .acct (rcpt R1), .acct (rcpt R2)]
      (splitIx 1001) ERR_RECIPIENT
    expect prog "split: recipients swapped"
      [.acct authA, .acct (vaultA 1_000_000 cfg), .acct (rcpt R1), .acct (rcpt R0), .acct (rcpt R2)]
      (splitIx 1001) ERR_RECIPIENT
    expect prog "split: signer is not the configured authority"
      (.acct { authA with key := MALLORY } :: ok.drop 1) (splitIx 1001) ERR_OWNER
    expect prog "split: authority did not sign" (.acct { authA with signer := false } :: ok.drop 1)
      (splitIx 1001) ERR_SIG
    expect prog "split: recipient read-only"
      [.acct authA, .acct (vaultA 1_000_000 cfg), .acct { rcpt R0 with writable := false }, .acct (rcpt R1), .acct (rcpt R2)]
      (splitIx 1001) ERR_ACCOUNT_DATA
    expect prog "split: same recipient passed twice (duplicate slot)"
      [.acct authA, .acct (vaultA 1_000_000 cfg), .acct (rcpt R0), .dup 2, .acct (rcpt R2)]
      (splitIx 1001) ERR_DUP
    expect prog "split: vault passed as a recipient (duplicate slot)"
      [.acct authA, .acct (vaultA 1_000_000 cfg), .dup 1, .acct (rcpt R1), .acct (rcpt R2)]
      (splitIx 1001) ERR_DUP
    expect prog "split: uninitialized vault" [.acct authA, .acct fresh, .acct (rcpt R0), .acct (rcpt R1), .acct (rcpt R2)]
      (splitIx 1001) ERR_KIND
    expect prog "split: vault owned by another program (spoofed config)"
      [.acct authA, .acct { vaultA 1_000_000 cfg with owner := MALLORY }, .acct (rcpt R0), .acct (rcpt R1), .acct (rcpt R2)]
      (splitIx 1001) ERR_OWNER
    expect prog "split: corrupted config (shares no longer sum to 10000)"
      [.acct authA, .acct (vaultA 1_000_000 (cfgData 5000 5000 5000 500 AUTH R0 R1 R2)), .acct (rcpt R0), .acct (rcpt R1), .acct (rcpt R2)]
      (splitIx 1001) ERR_ACCOUNT_DATA
    expect prog "split: recipient balance would overflow u64"
      [.acct authA, .acct (vaultA 1_000_000 cfg), .acct (rcpt R0 0xFFFFFFFFFFFFFF00), .acct (rcpt R1), .acct (rcpt R2)]
      (splitIx 1001) 0x0000001800000000
    expect prog "unknown opcode" ok (ByteArray.mk #[7]) ERR_IX
    expect prog "empty instruction data" ok .empty ERR_IX
    -- randomized differential: binary == model, shares sum exactly, dust < 3, conservation
    let mut rng : Rng := ⟨0xFEE5⟩
    let mut n := 0
    for _ in [0:400] do
      let (x, r1) := rng.next; let (y, r2) := r1.next; let (a, r3) := r2.nextWide; rng := r3
      let b1 := x % 10001; let b2 := y % (10001 - b1); let b0 := 10000 - b1 - b2
      let bal : UInt64 := 0xFFFFFFFFFFFF
      let amount := a % (bal - 500 + 1)
      let slots := [Slot.acct authA, .acct (vaultA bal (cfgData b0 b1 b2 500 AUTH R0 R1 R2)),
        .acct (rcpt R0), .acct (rcpt R1), .acct (rcpt R2)]
      if let some o ← runBoth prog "split differential" slots (splitIx amount) then
        n := n + 1
        let A := amount.toNat
        let s1 := A * b1.toNat / 10000; let s2 := A * b2.toNat / 10000; let s0 := A - s1 - s2
        let want := #[1_000_000, (bal.toNat - A).toUInt64, (1000 + s0).toUInt64,
          (1000 + s1).toUInt64, (1000 + s2).toUInt64]
        check (o.code == 0 && o.lamports == want) fun _ =>
          s!"split differential (A={A}, bps={b0}/{b1}/{b2}): got {o.code} {o.lamports}, want {want}"
        check (A * b0.toNat / 10000 ≤ s0 && s0 ≤ A * b0.toNat / 10000 + 2) fun _ => "dust bound violated"
    IO.println s!"   randomized split differential: {n} runs (binary == Lean model == exact shares)"

end LemmaTest.FeeSplitterTests
