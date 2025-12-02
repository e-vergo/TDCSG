import TDCSG.ProofOfMainTheorem
import Lean
import Std.Data.HashMap

open Lean Meta System

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

    let deps := getDirectDeps env current
    for dep in deps do
      if !visited.contains dep then
        worklist := worklist.push dep

  return visited

/-- Get all TDCSG declarations from environment -/
def getAllTDCSGDecls (env : Environment) : Array Name :=
  env.constants.map₁.toArray.filterMap fun (name, _) =>
    if isTDCSGDecl name then some name else none

/-- Get the file path for a declaration from its module name -/
def getFilePath (name : Name) : String :=
  let components := name.components
  if components.isEmpty then
    "TDCSG.lean"
  else
    let mut path := "TDCSG"
    for i in [1:components.length] do
      if let some comp := components[i]? then
        -- Check if this looks like a module name (starts with capital)
        let str := comp.toString
        if str.length > 0 && str.get! 0 |>.isUpper then
          path := path ++ "/" ++ str
        else
          -- This is likely a declaration name, stop here
          break
    path ++ ".lean"

/-- Group declarations by file -/
def groupByFile (decls : Array Name) : Std.HashMap String (Array Name) :=
  let mut result : Std.HashMap String (Array Name) := {}
  for decl in decls do
    let file := getFilePath decl
    match result.find? file with
    | some existing => result := result.insert file (existing.push decl)
    | none => result := result.insert file #[decl]
  result

/-- Generate deletion script for a file -/
def generateDeletionScript (filePath : String) (deadDecls : Array Name) : IO Unit := do
  let fullPath := filePath

  -- Check if file exists
  let exists ← fullPath.pathExists
  if !exists then
    IO.eprintln s!"  ⚠ File not found: {fullPath}"
    return

  IO.println s!"  # Commands to remove {deadDecls.size} declarations:"
  for decl in deadDecls do
    let shortName := decl.components.back!
    -- Generate sed command to delete the declaration and following blank lines
    IO.println s!"  # Delete: {shortName}"

def main (args : List String) : IO Unit := do
  let dryRun := args.contains "--dry-run"
  let force := args.contains "--force"

  if !force && !dryRun then
    IO.println "ERROR: This is a destructive operation. Use --dry-run to preview or --force to execute."
    IO.println ""
    IO.println "RECOMMENDED: Create a backup first:"
    IO.println "  git add -A && git commit -m 'backup before dead code deletion'"
    IO.println ""
    IO.println "Then run:"
    IO.println "  lake exe delete_dead_code --dry-run     # Preview changes"
    IO.println "  lake exe delete_dead_code --force       # Actually delete"
    return

  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `TDCSG.ProofOfMainTheorem}] {} 0

  -- Get all TDCSG declarations
  let allDecls := getAllTDCSGDecls env

  -- Find main theorem
  let mut mainTheoremOpt : Option Name := none
  for candidate in #[`GG5_infinite_at_critical_radius, `TDCSG.GG5_infinite_at_critical_radius] do
    if env.find? candidate |>.isSome then
      mainTheoremOpt := some candidate
      break

  let mainTheoremName := mainTheoremOpt.getD `GG5_infinite_at_critical_radius

  -- Get reachable declarations
  let reachable ← getTransitiveDeps env mainTheoremName

  -- Find dead code
  let deadCode := allDecls.filter fun name => !reachable.contains name

  IO.println "=== DEAD CODE DELETION ==="
  IO.println ""
  IO.println s!"Mode: {if dryRun then "DRY RUN (preview only)" else "EXECUTING"}"
  IO.println s!"Total declarations: {allDecls.size}"
  IO.println s!"Reachable: {reachable.size}"
  IO.println s!"Dead code: {deadCode.size}"
  IO.println ""

  -- Group by file
  let byFile := groupByFile deadCode

  IO.println s!"Affected files: {byFile.size}"
  IO.println ""

  -- Process each file
  for (file, decls) in byFile.toList do
    IO.println s!"{file}: {decls.size} declarations"
    deleteFromFile file decls dryRun
    IO.println ""

  if dryRun then
    IO.println "=== DRY RUN COMPLETE ==="
    IO.println ""
    IO.println "To actually delete, run:"
    IO.println "  lake exe delete_dead_code --force"
  else
    IO.println "=== DELETION COMPLETE ==="
    IO.println ""
    IO.println "Next steps:"
    IO.println "  1. Run: lake build"
    IO.println "  2. If build fails, investigate errors"
    IO.println "  3. Run: git diff (to review changes)"
    IO.println "  4. If satisfied: git add -A && git commit -m 'remove dead code'"
    IO.println "  5. If not satisfied: git restore ."
