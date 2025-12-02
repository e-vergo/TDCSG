import TDCSG.ProofOfMainTheorem
import Lean
import Lean.Server.Rpc.Basic

open Lean Meta System Server

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
  env.constants.map₁.toArray.filterMap fun (name, _) =>
    if isTDCSGDecl name then some name else none

/-- Search all TDCSG .lean files for a declaration -/
def findDeclarationInFiles (declName : String) : IO (Option (String × Nat)) := do
  -- Get all .lean files in TDCSG directory
  let dirs := #["TDCSG/Definitions", "TDCSG/Proofs", "TDCSG"]

  for dir in dirs do
    if !(← System.FilePath.pathExists dir) then
      continue

    let files ← System.FilePath.readDir dir
    for file in files do
      if file.path.toString.endsWith ".lean" then
        try
          let content ← IO.FS.readFile file.path.toString
          let linesArray := (content.splitOn "\n").toArray

          -- Search for the declaration
          for i in [0:linesArray.size] do
            let line := linesArray[i]!
            -- Check if line contains declaration keywords followed by our name
            if (line.splitOn declName).length > 1 then
              let keywords := ["def ", "theorem ", "lemma ", "axiom ", "inductive ", "structure "]
              if keywords.any (fun kw => (line.splitOn kw).length > 1) then
                return some (file.path.toString, i + 1)
        catch _ =>
          continue

  return none

def main : IO Unit := do
  initSearchPath (← findSysroot)

  let env ← importModules #[{module := `TDCSG.ProofOfMainTheorem}] {} 0

  -- Get all TDCSG declarations
  let allDecls := getAllTDCSGDecls env
  IO.eprintln s!"Total TDCSG declarations: {allDecls.size}"

  -- Find the main theorem
  let mut mainTheoremOpt : Option Name := none
  let candidates := #[
    `GG5_infinite_at_critical_radius,
    `TDCSG.ProofOfMainTheorem.GG5_infinite_at_critical_radius,
    `TDCSG.GG5_infinite_at_critical_radius,
    `TDCSG.CompoundSymmetry.GG5.GG5_is_infinite
  ]

  for candidate in candidates do
    if env.find? candidate |>.isSome then
      mainTheoremOpt := some candidate
      break

  let mainTheoremName := mainTheoremOpt.getD `GG5_infinite_at_critical_radius
  IO.eprintln s!"Main theorem: {mainTheoremName}"

  let reachable ← getTransitiveDeps env mainTheoremName
  IO.eprintln s!"Reachable from main theorem: {reachable.size}"

  -- Find dead code (declarations not reachable from main theorem)
  let mut deadCodeList : Array Name := #[]
  let mut allDeclSet : Std.HashSet Name := {}
  for name in allDecls do
    allDeclSet := allDeclSet.insert name
    if !reachable.contains name then
      deadCodeList := deadCodeList.push name

  let deadCode := deadCodeList.qsort (·.toString < ·.toString)

  IO.eprintln s!"Dead code: {deadCode.size}"
  IO.eprintln ""

  -- Print summary
  IO.println "=== DEAD CODE ANALYSIS ==="
  IO.println ""
  IO.println s!"Total declarations: {allDecls.size}"
  IO.println s!"Reachable from main theorem: {reachable.size} ({(reachable.size * 100) / allDecls.size}%)"
  IO.println s!"Dead code: {deadCode.size} ({(deadCode.size * 100) / allDecls.size}%)"
  IO.println ""

  -- Group by module (using first 3 components of name as approximation)
  let mut byModule : Std.HashMap String Nat := {}
  for name in deadCode do
    let components := name.components
    let moduleKey := if _ : components.length >= 3 then
      -- TDCSG.Definitions.Core or TDCSG.Proofs.GroupTheory
      s!"{components[0]!}.{components[1]!}.{components[2]!}"
    else if _ : components.length >= 2 then
      s!"{components[0]!}.{components[1]!}"
    else
      components[0]!.toString

    let currentCount := byModule.getD moduleKey 0
    byModule := byModule.insert moduleKey (currentCount + 1)

  IO.println "=== DEAD CODE BY MODULE (Top 20) ==="
  let moduleList := byModule.toList.insertionSort (fun a b => a.2 > b.2)
  let top20 := moduleList.take 20
  for (module, count) in top20 do
    IO.println s!"  {module}: {count} declarations"

  if moduleList.length > 20 then
    IO.println s!"  ... and {moduleList.length - 20} more modules"

  -- Save full list to file
  let h ← IO.FS.Handle.mk "docs/dead_code.txt" IO.FS.Mode.write
  h.putStrLn s!"Total: {allDecls.size} | Reachable: {reachable.size} | Dead: {deadCode.size}"
  h.putStrLn ""
  h.putStrLn "=== ALL UNREACHABLE DECLARATIONS ==="
  for name in deadCode do
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
      let declName := name.components.getLast!.toString
      let locationOpt ← findDeclarationInFiles declName
      let locationInfo := match locationOpt with
        | some (file, line) => s!" ({file}:{line})"
        | none => ""
      h.putStrLn s!"{name} ({kind}){locationInfo}"
    | none => h.putStrLn s!"{name}"
  h.flush

  IO.println ""
  IO.println s!"Full list saved to docs/dead_code.txt"
