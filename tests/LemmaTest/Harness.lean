/-
  LemmaTest.Harness — compile a Lean entrypoint with the real lean-svm pipeline and run it in
  the `LemmaTest.Sbpf` interpreter. Also: a deterministic PRNG and a tiny test-report monad.
-/
import Lean
import LeanSVM
import LemmaTest.Sbpf

namespace LemmaTest
open Lean LeanSVM LeanSVM.Compiler

/-- A program compiled by the production pipeline: symbolic instructions + `.rodata`. -/
structure Compiled where
  name   : Name
  insns  : Array SBPF.Insn
  rodata : ByteArray
  elfSize : Nat

/-- Compile `entry` from an already-imported environment. -/
def compile (env : Environment) (entry : Name) : Except String Compiled := do
  let res ← compileEntrypoint env entry {}
  let prog ← lowerEntrypoint env entry   -- deterministic; used only to recover `.rodata` bytes
  return { name := entry, insns := res.insns, rodata := prog.rodata, elfSize := res.elfSize }

/-- Import modules from the local Lake build tree. -/
def loadEnv (mods : Array Name) : IO Environment := do
  initSearchPath (← findSysroot)
  let sp ← searchPathRef.get
  searchPathRef.set ((".lake/build/lib/lean" : System.FilePath) :: sp)
  importModules (mods.map fun m => { module := m }) {}

def Compiled.run (c : Compiled) (input : ByteArray) : Sbpf.Halt × Sbpf.St :=
  Sbpf.execute c.insns c.rodata input

/-! ### Little-endian helpers -/

def u64le (v : UInt64) : ByteArray :=
  ⟨(List.range 8).toArray.map fun i => ((v >>> (8 * i).toUInt64) &&& 0xFF).toUInt8⟩

def readU64le (b : ByteArray) (off : Nat) : UInt64 := Id.run do
  let mut v : UInt64 := 0
  for i in [0:8] do v := v ||| ((b.get! (off + i)).toUInt64 <<< (8 * i).toUInt64)
  return v

/-! ### Deterministic PRNG (splitmix64) -/

structure Rng where
  s : UInt64

def Rng.next (r : Rng) : UInt64 × Rng :=
  let s := r.s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- A random value with a random bit-width, so small and boundary-sized values are common. -/
def Rng.nextWide (r : Rng) : UInt64 × Rng :=
  let (x, r) := r.next
  let (w, r) := r.next
  let bits := (w % 65)
  (if bits == 64 then x else x &&& ((1 <<< bits) - 1), r)

/-! ### Test reporting -/

structure Report where
  passed : Nat := 0
  failed : Array String := #[]

abbrev TestM := StateT Report IO

def check (ok : Bool) (msg : Unit → String) : TestM Unit :=
  modify fun r => if ok then { r with passed := r.passed + 1 }
                  else { r with failed := r.failed.push (msg ()) }

def section_ (title : String) : TestM Unit := IO.println s!"── {title}"

end LemmaTest
