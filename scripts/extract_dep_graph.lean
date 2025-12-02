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

/-- Check if a name is a compiler-generated auxiliary declaration -/
def isAuxDecl (name : Name) : Bool :=
  let nameStr := name.toString
  (nameStr.splitOn "._").length > 1

/-- Get the declaration kind as a string -/
def getDeclKind (info : ConstantInfo) : String :=
  match info with
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"
  | .opaqueInfo _ => "opaque"

/-- Get the DOT shape for a declaration kind -/
def getNodeShape (kind : String) : String :=
  match kind with
  | "theorem" => "ellipse"
  | "def" => "box"
  | "inductive" => "diamond"
  | "opaque" => "octagon"
  | _ => "box"

/-- Get the color based on namespace (green = formalized, matching blueprint style) -/
def getNodeColor (name : Name) : String :=
  let components := name.components
  if h : components.length >= 2 then
    let second := components[1]'(by omega)
    if second == `Definitions then
      "#90EE90"  -- Light green for definitions
    else if second == `CompoundSymmetry then
      "#7CFC00"  -- Lawn green for main proofs
    else if second == `Proofs then
      "#98FB98"  -- Pale green for supporting proofs
    else
      "#ADFF2F"  -- Green-yellow for other
  else
    "#ADFF2F"  -- Green-yellow for root-level

/-- Get direct dependencies (non-recursive) -/
def getDirectDeps (name : Name) : CoreM (Array Name) := do
  let env ← getEnv
  match env.find? name with
  | none => return #[]
  | some info =>
    -- Collect constants from type
    let typeConsts := collectConstants info.type

    -- Collect constants from value if available
    let valueConsts := match info with
      | .defnInfo val => collectConstants val.value
      | .thmInfo val => collectConstants val.value
      | _ => #[]

    -- Filter to TDCSG declarations only (excluding auxiliary)
    return (typeConsts ++ valueConsts).filter (fun n => isTDCSGDecl n && !isAuxDecl n)

/-- Escape a string for DOT format -/
def escapeDOT (s : String) : String :=
  s.replace "\\" "\\\\"
   |>.replace "\"" "\\\""
   |>.replace "\n" "\\n"

/-- Generate DOT node definition -/
def generateDOTNode (name : Name) (kind : String) : String :=
  let shape := getNodeShape kind
  let color := getNodeColor name
  let style := if color == "white" then "" else s!", style=filled, fillcolor=\"{color}\""
  s!"  \"{name}\" [shape={shape}, label=\"{escapeDOT (toString name)}\"{style}];"

/-- Generate DOT edge -/
def generateDOTEdge (src : Name) (tgt : Name) : String :=
  s!"  \"{src}\" -> \"{tgt}\";"

def main : IO Unit := do
  initSearchPath (← findSysroot)

  let env ← importModules #[{module := `TDCSG.ProofOfMainTheorem}] {} 0

  -- Get all TDCSG declarations directly from the environment (excluding auxiliary)
  let mut allDecls : Array Name := #[]
  for (name, _) in env.constants.map₁.toArray do
    if isTDCSGDecl name && !isAuxDecl name then
      allDecls := allDecls.push name

  let tdcsgDecls := allDecls.qsort (·.toString < ·.toString)
  let mut tdcsgDeclSet : Std.HashSet Name := {}
  for name in allDecls do
    tdcsgDeclSet := tdcsgDeclSet.insert name

  IO.eprintln s!"Found {tdcsgDecls.size} TDCSG declarations"

  -- Collect all edges (direct dependencies)
  let mut edges : Array (Name × Name) := #[]
  for decl in tdcsgDecls do
    let (deps, _) ← (getDirectDeps decl).toIO
      { fileName := "", fileMap := default }
      { env := env }

    for dep in deps do
      if tdcsgDeclSet.contains dep then
        edges := edges.push (decl, dep)

  -- Generate DOT output
  IO.println "digraph TDCSG {"
  IO.println "  rankdir=BT;"  -- Bottom to top (dependencies point upward)
  IO.println "  node [fontsize=10];"
  IO.println "  edge [color=gray, arrowsize=0.5];"
  IO.println ""

  -- Output nodes with styling
  for decl in tdcsgDecls do
    match env.find? decl with
    | some info =>
      let kind := getDeclKind info
      IO.println (generateDOTNode decl kind)
    | none => pure ()

  IO.println ""

  -- Output edges
  for (src, tgt) in edges do
    IO.println (generateDOTEdge src tgt)

  IO.println "}"
