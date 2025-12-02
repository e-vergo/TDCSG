import TDCSG.ProofOfMainTheorem
import Lean

open Lean Meta

/-- Collect all constant names from an expression -/
partial def collectConstants (e : Expr) : Array Name :=
  e.foldConsts #[] fun name acc =>
    if name.isInternal then acc else acc.push name

/-- Check if a name is in the TDCSG namespace -/
def isTDCSGDecl (name : Name) : Bool :=
  !name.components.isEmpty && name.components.head! == `TDCSG

/-- Get direct dependencies of a declaration -/
def getDirectDeps (env : Environment) (name : Name) : Array Name :=
  match env.find? name with
  | none => #[]
  | some info =>
    let typeConsts := collectConstants info.type
    let valueConsts := match info with
      | .defnInfo val => collectConstants val.value
      | .thmInfo val => collectConstants val.value
      | _ => #[]
    (typeConsts ++ valueConsts).filter isTDCSGDecl

/-- Get all transitive dependencies starting from a root declaration -/
def getTransitiveDeps (env : Environment) (root : Name) : IO (Std.HashSet Name) := do
  let mut visited : Std.HashSet Name := {}
  let mut worklist : Array Name := #[root]
  let mut idx := 0

  while idx < worklist.size do
    let current := worklist[idx]!
    idx := idx + 1

    if visited.contains current then
      continue

    visited := visited.insert current

    -- Get dependencies
    let deps := getDirectDeps env current
    for dep in deps do
      if !visited.contains dep then
        worklist := worklist.push dep

  return visited

/-- Get all TDCSG declarations from environment -/
def getAllTDCSGDecls (env : Environment) : Array Name :=
  let mut result : Array Name := #[]
  for (name, _) in env.constants.map₁.toArray do
    if isTDCSGDecl name then
      result := result.push name
  result

def main : IO Unit := do
  initSearchPath (← findSysroot)

  let env ← importModules #[{module := `TDCSG.ProofOfMainTheorem}] {} 0

  -- Get all TDCSG declarations
  let allDecls := getAllTDCSGDecls env
  IO.eprintln s!"Total TDCSG declarations: {allDecls.size}"

  -- Get transitive dependencies from main theorem
  let mainTheoremName := `TDCSG.ProofOfMainTheorem.GG5_infinite_at_critical_radius
  IO.eprintln s!"Computing transitive dependencies from {mainTheoremName}..."

  let reachable ← getTransitiveDeps env mainTheoremName
  IO.eprintln s!"Reachable declarations: {reachable.size}"

  -- Find dead code (declarations not reachable from main theorem)
  let mut deadCodeList : Array Name := #[]
  let mut allDeclSet : Std.HashSet Name := {}
  for name in allDecls do
    allDeclSet := allDeclSet.insert name
    if !reachable.contains name then
      deadCodeList := deadCodeList.push name

  let deadCode := deadCodeList.qsort (·.toString < ·.toString)

  IO.eprintln s!"Dead code declarations: {deadCode.size}"
  IO.eprintln ""

  if deadCode.size > 0 then
    IO.println "=== DEAD CODE ANALYSIS ==="
    IO.println ""
    IO.println s!"Total declarations: {allDecls.size}"
    IO.println s!"Reachable from main theorem: {reachable.size}"
    IO.println s!"Dead code: {deadCode.size} ({(deadCode.size * 100) / allDecls.size}%)"
    IO.println ""
    IO.println "=== UNREACHABLE DECLARATIONS ==="
    for name in deadCode do
      -- Get file location if available
      match env.find? name with
      | some info =>
        let kind := match info with
          | .defnInfo _ => "def"
          | .thmInfo _ => "theorem"
          | .axiomInfo _ => "axiom"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
          | .quotInfo _ => "quot"
          | .opaqueInfo _ => "opaque"
        IO.println s!"{name} ({kind})"
      | none => IO.println s!"{name}"
  else
    IO.println "=== NO DEAD CODE FOUND ==="
    IO.println ""
    IO.println "All {allDecls.size} declarations are reachable from the main theorem!"
