/-
  Main.lean — `lean-svm` Native Lean 4 → Solana sBPF v3 Compiler CLI

  Usage:
    lake exe lean-svm build <Module> <DeclName> -o <out.so> [--dump-ir] [--dump-asm]
-/
import Lean
import LeanSVM

open Lean
open LeanSVM.Compiler
open LeanSVM.SBPF

private def usage : String :=
  "lean-svm: Native Lean 4 → Solana sBPF v3 Optimizing Compiler\n\n" ++
  "Usage:\n" ++
  "  lean-svm build <ModuleName> <EntrypointDecl> -o <output.so> [options]\n\n" ++
  "Options:\n" ++
  "  -o <path>         Output Solana sBPF v3 ELF64 .so file path (required)\n" ++
  "  --dump-ir         Print raw and optimized SbfIR to stdout\n" ++
  "  --dump-asm        Print generated sBPF v3 assembly to stdout\n" ++
  "  -h, --help        Show this help message\n\n" ++
  "Example:\n" ++
  "  lake exe lean-svm build Examples.Counter Examples.Counter.entrypoint -o build/counter.so --dump-asm\n"

private def parseName (s : String) : Name :=
  s.splitOn "." |>.foldl (fun acc part => Name.str acc part) Name.anonymous

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["-h"] | ["--help"] =>
    IO.println usage
    return 0
  | "build" :: modStr :: declStr :: rest =>
    let mut outPath? : Option System.FilePath := none
    let mut dumpIR := false
    let mut dumpAsm := false
    let mut cur := rest
    while !cur.isEmpty do
      match cur with
      | "-o" :: p :: tail =>
        outPath? := some ⟨p⟩
        cur := tail
      | "--dump-ir" :: tail =>
        dumpIR := true
        cur := tail
      | "--dump-asm" :: tail =>
        dumpAsm := true
        cur := tail
      | [] => break
      | flag :: _ =>
        IO.eprintln s!"error: unknown argument '{flag}'"
        return 1

    let some outPath := outPath?
      | do IO.eprintln "error: missing required -o <output.so> argument"; return 1

    -- Initialize Lean search path including `.lake/build/lib/lean`
    initSearchPath (← findSysroot)
    let lakeLib : System.FilePath := ".lake/build/lib/lean"
    let sp ← searchPathRef.get
    searchPathRef.set (lakeLib :: sp)

    let modName := parseName modStr
    let declName := parseName declStr

    let env ← try
      importModules #[{ module := modName }] {}
    catch e =>
      IO.eprintln s!"error: failed to import Lean module '{modStr}': {e}"
      IO.eprintln "hint: run `lake build` first so the module .olean is up to date"
      return 1

    let opts : CompileOptions := { dumpIR, dumpAsm }
    match compileEntrypoint env declName opts with
    | .error err =>
      IO.eprintln s!"compile error ({declStr}): {err}"
      return 1
    | .ok res =>
      if let some parent := outPath.parent then
        IO.FS.createDirAll parent
      IO.FS.writeBinFile outPath res.elfBytes
      if dumpIR then
        IO.println "=== RAW SbfIR ==="
        IO.println res.rawIrDump
        IO.println "\n=== OPTIMIZED SbfIR ==="
        IO.println res.optIrDump
        IO.println ""
      if dumpAsm then
        IO.println "=== sBPF ASSEMBLY ==="
        IO.println res.asmDump
        IO.println ""
      IO.println res.formatStats
      IO.println s!"  output       : {outPath}"
      return 0
  | _ =>
    IO.eprintln "error: invalid arguments\n"
    IO.eprintln usage
    return 1
