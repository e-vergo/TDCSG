import TDCSG.ProofOfMainTheorem
import Lean

open Lean Meta

/-- Collect all constant names from an expression -/
partial def collectConstants (e : Expr) : Array Name :=
  e.foldConsts #[] fun name acc =>
    if name.isInternal then acc else acc.push name

/-- Get all transitive dependencies of a declaration (non-Mathlib) -/
partial def getTransitiveDeps (visited : Std.HashSet Name) (name : Name) :
    CoreM (Std.HashSet Name) := do
  if visited.contains name then
    return visited

  -- Skip Mathlib, Init, Lean, Batteries, Std
  let components := name.components
  if components.isEmpty then return visited

  let firstComponent := components.head!
  if firstComponent == `Mathlib ||
     firstComponent == `Init ||
     firstComponent == `Lean ||
     firstComponent == `Batteries ||
     firstComponent == `Std then
    return visited

  let visited := visited.insert name

  -- Get the constant info
  let env ← getEnv
  match env.find? name with
  | none => return visited
  | some info =>
    -- Collect constants from type
    let typeConsts := collectConstants info.type

    -- Collect constants from value if available
    let valueConsts := match info with
      | .defnInfo val => collectConstants val.value
      | .thmInfo val => collectConstants val.value
      | _ => #[]

    -- Recursively process all dependencies
    let mut newVisited := visited
    for c in typeConsts ++ valueConsts do
      newVisited ← getTransitiveDeps newVisited c

    return newVisited

def main : IO Unit := do
  initSearchPath (← findSysroot)

  let env ← importModules #[{module := `TDCSG.ProofOfMainTheorem}] {} 0

  let mainTheoremName := `GG5_infinite_at_critical_radius

  IO.println s!"Extracting dependency graph for: {mainTheoremName}"
  IO.println ""

  let (deps, _) ← (getTransitiveDeps {} mainTheoremName).toIO
    { fileName := "", fileMap := default }
    { env := env }

  -- Filter to TDCSG namespace
  let tdcsgDepsArray := deps.toArray.filter fun name =>
    !name.components.isEmpty && name.components.head! == `TDCSG

  IO.println s!"Found {tdcsgDepsArray.size} TDCSG declarations (excluding Mathlib)"
  IO.println ""

  -- Group by second namespace component (file grouping)
  let mut byFile : Std.HashMap String (Array Name) := {}
  for name in tdcsgDepsArray do
    let fileKey :=
      if name.components.length ≥ 2 then
        toString (name.components.take 2)
      else
        toString name.components
    let existing := byFile.getD fileKey #[]
    byFile := byFile.insert fileKey (existing.push name)

  IO.println "=== Declarations by namespace ==="
  for (file, decls) in byFile.toArray.qsort (·.1 < ·.1) do
    IO.println s!"\n{file} ({decls.size} declarations):"
    for decl in (decls.qsort (·.toString < ·.toString)).toList.take 20 do
      IO.println s!"  - {decl}"
    if decls.size > 20 then
      IO.println s!"  ... and {decls.size - 20} more"

  IO.println s!"\n=== Total: {tdcsgDepsArray.size} declarations ==="
