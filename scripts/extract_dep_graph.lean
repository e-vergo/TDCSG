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

/-- Get the color based on namespace and dead code status -/
def getNodeColor (name : Name) (deadCodeSet : Std.HashSet Name) : String :=
  -- Dead code is shown in grey/red
  if deadCodeSet.contains name then
    "#FFB6C1"  -- Light pink for dead code (unreachable)
  else
    -- Live code colored by namespace (green = formalized, matching blueprint style)
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
def generateDOTNode (name : Name) (kind : String) (deadCodeSet : Std.HashSet Name) : String :=
  let shape := getNodeShape kind
  let color := getNodeColor name deadCodeSet
  let style := s!", style=filled, fillcolor=\"{color}\""
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

  -- Compute reachability from main theorem to identify dead code
  let proofTheoremCandidates := #[
    `TDCSG.ProofOfMainTheorem.GG5_infinite_at_critical_radius,
    `TDCSG.GG5_infinite_at_critical_radius
  ]

  let mainTheoremNames := #[
    `StatementOfTheorem,
    `GG5_At_Critical_radius,
    `TwoDiskCompoundSymmetryGroup,
    `genA_n_perm,
    `genB_n_perm
  ]

  let mut reachable : Std.HashSet Name := {}

  -- Find and trace from proof theorem
  for candidate in proofTheoremCandidates do
    if env.find? candidate |>.isSome then
      IO.eprintln s!"Proof theorem: {candidate}"
      reachable := reachable.insert candidate

      -- BFS to find all dependencies
      let mut worklist : Array Name := #[candidate]
      let mut idx := 0

      while idx < worklist.size do
        let current := worklist[idx]!
        idx := idx + 1

        let (deps, _) ← (getDirectDeps current).toIO
          { fileName := "", fileMap := default }
          { env := env }

        for dep in deps do
          if !reachable.contains dep && tdcsgDeclSet.contains dep then
            reachable := reachable.insert dep
            worklist := worklist.push dep

      break

  -- Trace from MainTheorem declarations
  for name in mainTheoremNames do
    if env.find? name |>.isSome then
      IO.eprintln s!"MainTheorem: {name}"
      if !reachable.contains name then
        reachable := reachable.insert name

        -- BFS from this theorem
        let mut worklist : Array Name := #[name]
        let mut idx := 0

        while idx < worklist.size do
          let current := worklist[idx]!
          idx := idx + 1

          let (deps, _) ← (getDirectDeps current).toIO
            { fileName := "", fileMap := default }
            { env := env }

          for dep in deps do
            if !reachable.contains dep && tdcsgDeclSet.contains dep then
              reachable := reachable.insert dep
              worklist := worklist.push dep

  -- Compute dead code (unreachable)
  let mut deadCodeSet : Std.HashSet Name := {}
  for name in allDecls do
    if !reachable.contains name then
      deadCodeSet := deadCodeSet.insert name

  IO.eprintln s!"Reachable: {reachable.size}, Dead code: {deadCodeSet.size}"

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
  IO.println "  // Legend"
  IO.println "  subgraph cluster_legend {"
  IO.println "    label=\"Color Key\";"
  IO.println "    \"legend_defs\" [label=\"Definitions\", style=filled, fillcolor=\"#90EE90\", shape=box];"
  IO.println "    \"legend_proofs\" [label=\"Proofs\", style=filled, fillcolor=\"#98FB98\", shape=ellipse];"
  IO.println "    \"legend_dead\" [label=\"Dead Code (Unreachable)\", style=filled, fillcolor=\"#FFB6C1\", shape=box];"
  IO.println "  }"
  IO.println ""

  -- Output nodes with styling
  for decl in tdcsgDecls do
    match env.find? decl with
    | some info =>
      let kind := getDeclKind info
      IO.println (generateDOTNode decl kind deadCodeSet)
    | none => pure ()

  IO.println ""

  -- Output edges
  for (src, tgt) in edges do
    IO.println (generateDOTEdge src tgt)

  IO.println "}"
