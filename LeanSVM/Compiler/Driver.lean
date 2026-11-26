/-
  LeanSVM.Compiler.Driver
  End-to-end native Lean 4 → Solana sBPF compiler pipeline:
    Lean 4 LCNF (Mono) → Lower (SROA, Ghost Erasure, Scoped Stack Reuse, Helper Outlining)
    → Optimize (ConstFold, AddrFold, StackFold, StoreImm, CSE, BranchFusion, TailMerge, DCE)
    → RegAlloc (Exact Liveness, Coalescing Linear Scan) → CodeGen → Peephole → ELF64 `.so`
-/
import Lean
import LeanSVM.Compiler.IR
import LeanSVM.Compiler.Lower
import LeanSVM.Compiler.Optimize
import LeanSVM.Compiler.RegAlloc
import LeanSVM.Compiler.CodeGen
import LeanSVM.Compiler.Validate
import LeanSVM.SBPF.ISA
import LeanSVM.SBPF.ELF

namespace LeanSVM.Compiler

open Lean

structure CompileOptions where
  sbpfVersion : SBPF.Version := .v0
  dumpIR      : Bool := false
  dumpAsm     : Bool := false
  deriving Repr

structure CompileResult where
  entryName   : String
  sbpfVersion : SBPF.Version
  elfBytes    : ByteArray
  insns       : Array SBPF.Insn
  insnCount   : Nat
  textBytes   : Nat
  rodataBytes : Nat
  stackBytes  : Nat
  spillCount  : Nat
  helperCount : Nat := 0
  heapBytes   : Nat := 0  -- Guaranteed 0 by construction!
  elfSize     : Nat
  rawIrDump   : String
  optIrDump   : String
  asmDump     : String

/-- Compile a Lean 4 Solana entrypoint declaration from `env` directly into a Solana sBPF ELF64 `.so`. -/
def compileEntrypoint (env : Environment) (entryName : Name) (opts : CompileOptions := {}) :
    Except String CompileResult := do
  -- Stage 1: LCNF Mono → SbfIR
  let prog ← lowerEntrypoint env entryName
  let rawIrDump :=
    if opts.dumpIR then
      String.intercalate "\n\n" ((prog.entry :: prog.helpers.toList).map formatFunc)
    else ""

  -- Stage 2: Aggressive SSA IR Optimization (ConstFold, VRange, AddrFold, StackFold, StoreImm, CSE, TailMerge, DCE)
  --          + Interprocedural Dead Helper Elimination
  let optEntry := optimizeFunc prog.entry
  let optHelpers := prog.helpers.map optimizeFunc
  let optProg : Program := removeDeadHelpers { entry := optEntry, helpers := optHelpers, rodata := prog.rodata }
  let optIrDump :=
    if opts.dumpIR then
      String.intercalate "\n\n" ((optProg.entry :: optProg.helpers.toList).map formatFunc)
    else ""

  -- Stage 3: Formally Verified Translation Validation (CFG, Immediates, Liveness & RegAlloc)
  --          + Direct sBPF CodeGen + Peephole Optimization
  validateProgramCFG optProg
  let entryAlloc := allocateRegisters optProg.entry
  validateFuncAlloc optProg.entry entryAlloc
  let mut allInsns := generateFuncCodeWithAlloc optProg.entry entryAlloc
  let mut maxStack := entryAlloc.totalStackBytes
  let mut totalSpills := entryAlloc.spillCount
  for h in optProg.helpers do
    let hAlloc := allocateRegisters h
    validateFuncAlloc h hAlloc
    allInsns := allInsns ++ generateFuncCodeWithAlloc h hAlloc
    maxStack := max maxStack hAlloc.totalStackBytes
    totalSpills := totalSpills + hAlloc.spillCount
  let insns := SBPF.peepholeOptimize allInsns
  let alloc : AllocResult := { entryAlloc with totalStackBytes := maxStack, spillCount := totalSpills }
  let helperCount := optProg.helpers.size
  let asmDump := if opts.dumpAsm then SBPF.formatProgram insns else ""

  -- Stage 4: Direct Native ELF64 `.so` Linking & Serialization
  let (elfBytes, assembled) ← SBPF.emitElf insns prog.rodata opts.sbpfVersion

  return {
    entryName   := entryName.toString
    sbpfVersion := opts.sbpfVersion
    elfBytes    := elfBytes
    insns       := insns
    insnCount   := assembled.insnCount
    textBytes   := assembled.bytes.size
    rodataBytes := prog.rodata.size
    stackBytes  := alloc.totalStackBytes
    spillCount  := alloc.spillCount
    helperCount := helperCount
    heapBytes   := 0
    elfSize     := elfBytes.size
    rawIrDump   := rawIrDump
    optIrDump   := optIrDump
    asmDump     := asmDump
  }

def CompileResult.formatStats (r : CompileResult) : String :=
  let verStr := match r.sbpfVersion with | .v0 => "sBPF v0" | .v3 => "sBPF v3"
  s!"[lean-svm] Compiled {r.entryName} ({verStr})\n" ++
  s!"  instructions : {r.insnCount} (helpers: {r.helperCount})\n" ++
  s!"  .text size   : {r.textBytes} bytes\n" ++
  s!"  .rodata size : {r.rodataBytes} bytes\n" ++
  s!"  stack frame  : {r.stackBytes} bytes (spills: {r.spillCount})\n" ++
  s!"  heap alloc   : {r.heapBytes} bytes (zero-allocation)\n" ++
  s!"  ELF .so size : {r.elfSize} bytes"

end LeanSVM.Compiler
