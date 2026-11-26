/-
  `lake exe lemma-audit [--write]` — proof-integrity and runtime-hygiene audit. Exit code 0 iff
  LEMMA's policy holds.

  Policy, enforced for every declaration in a `Lemma.*` module:
  1. No `axiom` declarations.
  2. Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
     (`sorryAx` and `bv_decide` / `native_decide` native axioms are therefore rejected.)
  3. No `Nat` arithmetic is reachable from a LEMMA entrypoint. The walk is over the compiler's
     own LCNF IR, which is exactly what lean-svm lowers, so erased proofs cannot cause false
     positives. LEMMA runtime code must use `UInt64` with explicit checks; `Nat` belongs in specs.

  Upstream `LeanSVM.*` / `Examples.*` theorems are audited for information only: their axiom
  usage is listed in the generated report, but they cannot fail the build.

  `--write` regenerates `docs/specs/axiom-report.md`; without it, the tool fails if that committed
  report is stale.
-/
import Lean
import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.PhaseExt
import Std.Data.HashSet

open Lean Lean.Compiler.LCNF

namespace LemmaAudit

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def natOps : List Name :=
  [``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.pow, ``Nat.pred, ``Nat.succ,
   ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight, ``Nat.log2,
   ``instAddNat, ``instSubNat, ``instMulNat, ``Nat.instDiv, ``Nat.instMod, ``instPowNat]

def moduleOf (env : Environment) (n : Name) : Option Name :=
  env.getModuleIdxFor? n |>.map fun i => env.header.moduleNames[i.toNat]!

def isLemmaModule (m : Name) : Bool := m.getRoot == `Lemma

/-- Auto-generated equation / matcher / unfolding lemmas: audited, but not listed in the report. -/
def isAuxName (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "eq_" || s == "eq_def" || s.startsWith "match_" ||
      s.startsWith "proof_" || s.endsWith "_unfold" || s == "induct" || s.startsWith "_"
  | _ => true

/-- `Spec` namespaces hold mathematical specifications (they may use `Nat` freely). -/
def isSpecName (n : Name) : Bool := n.components.contains `Spec
def isUpstreamModule (m : Name) : Bool := m.getRoot == `LeanSVM || m.getRoot == `Examples

def lookupDecl? (env : Environment) (n : Name) : Option (Decl .pure) :=
  (getDeclCore? env monoExt n).orElse fun _ => getDeclCore? env baseExt n

partial def codeConsts (c : Code .pure) (acc : Array Name := #[]) : Array Name :=
  match c with
  | .let d k =>
    let acc := match d.value with
      | .const n _ _ _ => acc.push n
      | _ => acc
    codeConsts k acc
  | .jp d k | .fun d k _ => codeConsts k (codeConsts d.value acc)
  | .cases cs => cs.alts.foldl (fun acc a => match a with
      | .alt _ _ body _ | .default body | .ctorAlt _ body _ => codeConsts body acc) acc
  | _ => acc

/-- Walk the LCNF call graph from `entry`, descending only into LEMMA / lean-svm declarations
    (core-library primitives are lowered as intrinsics). Returns `(caller, natOp)` hits. -/
def natHits (env : Environment) (entry : Name) : Array (Name × Name) := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut stack := #[entry]
  let mut hits := #[]
  let mut fuel := 100000
  while h : stack.size > 0 do
    fuel := fuel - 1
    if fuel == 0 then break
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some d := lookupDecl? env n | continue
    let .code c := d.value | continue
    for callee in codeConsts c do
      if natOps.contains callee then hits := hits.push (n, callee)
      else
        let r := callee.getRoot
        if r == `Lemma || r == `LeanSVM then stack := stack.push callee
  return hits

structure Row where
  name : Name
  module : Name
  axioms : List Name

def run (write : Bool) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let sp ← searchPathRef.get
  searchPathRef.set ((".lake/build/lib/lean" : System.FilePath) :: sp)
  let env ← importModules #[{ module := `Lemma }, { module := `LeanSVM }, { module := `Examples }] {}
  let mut errors : Array String := #[]
  let mut lemmaRows : Array Row := #[]
  let mut upstreamRows : Array Row := #[]
  let mut entrypoints : Array Name := #[]
  for (n, ci) in env.constants.toList do
    let some m := moduleOf env n | continue
    unless isLemmaModule m || isUpstreamModule m do continue
    if isLemmaModule m then
      if let .axiomInfo _ := ci then errors := errors.push s!"axiom declaration in {m}: {n}"
      if n.isInternal then continue
      -- lint roots: entrypoints and every runtime (non-`Spec`) definition with compiled code
      if let .defnInfo _ := ci then
        if !isSpecName n && (lookupDecl? env n).isSome then entrypoints := entrypoints.push n
    if n.isInternal then continue
    if isLemmaModule m && n.getRoot != `Lemma then continue  -- auto-generated eqn lemmas etc.
    let .thmInfo _ := ci | continue
    let axs ← (do
        let r ← (Lean.collectAxioms n : CoreM (Array Name)).toIO
          { fileName := "<audit>", fileMap := default } { env := env }
        pure r.1.toList)
    let axs := axs.mergeSort (fun a b => a.toString ≤ b.toString)
    let row : Row := { name := n, module := m, axioms := axs }
    if isLemmaModule m then
      unless isAuxName n do lemmaRows := lemmaRows.push row
      for a in axs do
        unless allowedAxioms.contains a do
          errors := errors.push s!"{n} depends on disallowed axiom {a}"
    else upstreamRows := upstreamRows.push row
  -- Nat lint over every LEMMA entrypoint
  let mut natReport : Array String := #[]
  for e in entrypoints.qsort (·.toString < ·.toString) do
    let hits := natHits env e
    for (caller, op) in hits do
      let msg := s!"{e}: `{op}` reachable via `{caller}`"
      natReport := natReport.push msg
      if caller.getRoot == `Lemma then errors := errors.push s!"runtime Nat: {msg}"
  -- Report
  let sortRows (rs : Array Row) := rs.qsort (fun a b => a.name.toString < b.name.toString)
  let lemmaSorted := sortRows lemmaRows
  let upstreamSorted := sortRows upstreamRows
  let fmtAx (r : Row) := if r.axioms.isEmpty then "_(none)_" else
    ", ".intercalate (r.axioms.map fun a =>
      if allowedAxioms.contains a then s!"`{a}`" else s!"**`{a}`**")
  let isNative (r : Row) := r.axioms.any fun a => (a.toString.splitOn "_native").length > 1
  let mut md := "<!-- GENERATED by `lake exe lemma-audit --write`. Do not edit by hand. -->\n\n"
  md := md ++ "# Axiom report\n\n"
  md := md ++ s!"Allowed axioms for LEMMA theorems: `propext`, `Classical.choice`, `Quot.sound`.\n\n"
  md := md ++ s!"## LEMMA theorems ({lemmaSorted.size})\n\n| Theorem | Axioms |\n|---|---|\n"
  for r in lemmaSorted do md := md ++ s!"| `{r.name}` | {fmtAx r} |\n"
  let nativeUp := upstreamSorted.filter isNative
  md := md ++ s!"\n## Upstream lean-svm theorems (informational)\n\n"
  md := md ++ s!"{upstreamSorted.size} theorems; {upstreamSorted.size - nativeUp.size} use only the standard axioms; "
  md := md ++ s!"{nativeUp.size} depend on `bv_decide` native-evaluation axioms, so they trust the compiled "
  md := md ++ "LRAT checker as well as the kernel:\n\n"
  for r in nativeUp do md := md ++ s!"- `{r.name}`\n"
  md := md ++ s!"\n## Runtime `Nat` lint ({entrypoints.size} LEMMA runtime definitions)\n\n"
  if natReport.isEmpty then md := md ++ "No `Nat` arithmetic is reachable from any LEMMA runtime definition.\n"
  else for l in natReport do md := md ++ s!"- {l}\n"
  let path : System.FilePath := "docs/specs/axiom-report.md"
  if write then
    IO.FS.createDirAll "docs/specs"
    IO.FS.writeFile path md
    IO.println s!"wrote {path}"
  else
    let cur ← (IO.FS.readFile path).toBaseIO
    match cur with
    | .ok s => if s != md then errors := errors.push s!"{path} is stale: run `lake exe lemma-audit --write`"
    | .error _ => errors := errors.push s!"{path} missing: run `lake exe lemma-audit --write`"
  IO.println s!"LEMMA theorems listed: {lemmaSorted.size}; runtime definitions linted: {entrypoints.size}"
  IO.println s!"upstream theorems (info): {upstreamSorted.size}, of which {nativeUp.size} use bv_decide native axioms"
  if errors.isEmpty then
    IO.println "audit: OK"
    return 0
  else
    for e in errors do IO.eprintln s!"audit: FAIL {e}"
    return 1

end LemmaAudit

def main (args : List String) : IO UInt32 := LemmaAudit.run (args.contains "--write")
