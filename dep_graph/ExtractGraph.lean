import TDCSG.ProofOfMainTheorem
import Lean
import Lean.Data.Json

open Lean Meta System

/-- Collect all constant names from an expression -/
partial def collectConstants (e : Expr) : Array Name :=
  e.foldConsts #[] fun name acc =>
    if name.isInternal then acc else acc.push name

/-- Check if a name is in the TDCSG namespace or is a root-level main theorem -/
def isTDCSGDecl (name : Name) : Bool :=
  let mainTheoremNames := [
    `StatementOfTheorem,
    `GG5_At_Critical_radius,
    `GG5_infinite_at_critical_radius
  ]
  mainTheoremNames.contains name ||
  (!name.components.isEmpty && name.components.head! == `TDCSG)

/-- Check if a name is a compiler-generated auxiliary declaration -/
def isAuxDecl (name : Name) : Bool :=
  let nameStr := name.toString
  -- Compiler-generated proof obligations: ._proof, ._simp, etc.
  (nameStr.splitOn "._").length > 1 ||
  -- Derived instances: instDecidableEq, instRepr, etc.
  (nameStr.splitOn "inst").length > 1 && (
    (nameStr.splitOn "Decidable").length > 1 ||
    (nameStr.splitOn "Repr").length > 1 ||
    (nameStr.splitOn "Inhabited").length > 1 ||
    (nameStr.splitOn "BEq").length > 1
  ) ||
  -- Macro expansions
  (nameStr.splitOn "_aux_").length > 1 ||
  (nameStr.splitOn "macroRules").length > 1 ||
  (nameStr.splitOn "«").length > 1  -- Escaped identifiers from macros

/-- Get the declaration kind as a string -/
def getDeclKindStr (info : ConstantInfo) : String :=
  match info with
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"
  | .opaqueInfo _ => "opaque"

/-- JSON structure for a node -/
structure NodeInfo where
  id : String
  label : String
  «type» : String
  «namespace» : Array String
  file : String
  line : Nat
  docstring : String
  paperRefs : Array String
  isMainTheorem : Bool
  deriving Repr

instance : ToJson NodeInfo where
  toJson n := Json.mkObj [
    ("id", toJson n.id),
    ("label", toJson n.label),
    ("type", toJson n.type),
    ("namespace", toJson n.namespace),
    ("file", toJson n.file),
    ("line", toJson n.line),
    ("docstring", toJson n.docstring),
    ("paperRefs", toJson n.paperRefs),
    ("isMainTheorem", toJson n.isMainTheorem)
  ]

/-- JSON structure for an edge -/
structure EdgeInfo where
  source : String
  target : String
  deriving Repr

instance : ToJson EdgeInfo where
  toJson e := Json.mkObj [
    ("source", toJson e.source),
    ("target", toJson e.target)
  ]

/-- JSON structure for the complete graph -/
structure GraphData where
  nodes : Array NodeInfo
  edges : Array EdgeInfo
  deriving Repr

instance : ToJson GraphData where
  toJson g := Json.mkObj [
    ("nodes", toJson g.nodes),
    ("edges", toJson g.edges)
  ]

/-- Extract source location (file and line) for a declaration using file search -/
def findDeclarationInFiles (env : Environment) (name : Name) : IO (Option (String × Nat)) := do
  -- Get module name
  match env.getModuleFor? name with
  | none => return none
  | some modName =>
    let modComponents := modName.components
    let filePath := String.intercalate "/" (modComponents.map toString) ++ ".lean"

    -- Try to read the file
    let fullPath : System.FilePath := filePath
    if !(← fullPath.pathExists) then
      return some (filePath, 1)

    try
      let content ← IO.FS.readFile fullPath
      let lines := content.splitOn "\n"
      let declName := name.components.getLast!.toString

      -- Search for declaration (look for keyword followed by the exact declaration name)
      for i in [0:lines.length] do
        let line := lines[i]!
        -- Match patterns like "def DeclName", "theorem DeclName ", etc.
        let keywords := ["def ", "theorem ", "lemma ", "axiom ", "inductive ", "structure ", "class "]
        for kw in keywords do
          -- Check if line contains "keyword declName" (with space or : after declName)
          if (line.splitOn (kw ++ declName)).length > 1 then
            let afterKeyword := (line.splitOn (kw ++ declName))[1]!
            -- Verify it's followed by space, colon, or open paren (not just a prefix match)
            if afterKeyword.isEmpty ||
               afterKeyword.front == ' ' ||
               afterKeyword.front == ':' ||
               afterKeyword.front == '(' then
              return some (filePath, i + 1)

      return some (filePath, 1)
    catch _ =>
      return some (filePath, 1)

/-- Extract docstring for a declaration (stub for now) -/
def getDocstring (_env : Environment) (_name : Name) : String :=
  ""  -- Docstrings not easily accessible in Lean 4 without LSP

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
    (typeConsts ++ valueConsts).filter (fun n => isTDCSGDecl n && !isAuxDecl n)

/-- Check if a name is a main theorem -/
def isMainTheoremName (name : Name) : Bool :=
  let mainTheorems := #[
    `GG5_infinite_at_critical_radius,
    `StatementOfTheorem,
    `GG5_At_Critical_radius
  ]
  -- Check both with and without namespace prefix
  mainTheorems.contains name ||
  mainTheorems.any (fun mt => name.toString.endsWith mt.toString)

/-- Main extraction function -/
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `TDCSG.ProofOfMainTheorem}] {} 0

  -- Collect all TDCSG declarations (exclude auxiliary)
  let mut allDecls : Array Name := #[]
  for (name, _) in env.constants.map₁.toArray do
    if isTDCSGDecl name && !isAuxDecl name then
      allDecls := allDecls.push name

  IO.eprintln s!"Found {allDecls.size} TDCSG declarations"

  -- Build set for fast lookup
  let mut declSet : Std.HashSet Name := {}
  for name in allDecls do
    declSet := declSet.insert name

  -- Extract nodes
  let mut nodes : Array NodeInfo := #[]
  for name in allDecls do
    match env.find? name with
    | none => continue
    | some info =>
      -- Extract metadata
      let kind := getDeclKindStr info
      let components := name.components
      let label := components.getLast!.toString
      let namespaceList := components.dropLast.toArray.map toString

      let (file, line) ← findDeclarationInFiles env name
        |>.map (·.getD ("unknown", 1))

      let docstring := getDocstring env name
      let isMainTheorem := isMainTheoremName name

      let node : NodeInfo := {
        id := name.toString
        label := label
        «type» := kind
        «namespace» := namespaceList
        file := file
        line := line
        docstring := docstring
        paperRefs := #[]
        isMainTheorem := isMainTheorem
      }
      nodes := nodes.push node

  IO.eprintln s!"Extracted {nodes.size} nodes"

  -- Extract edges
  let mut edges : Array EdgeInfo := #[]
  for name in allDecls do
    let deps := getDirectDeps env name
    for dep in deps do
      if declSet.contains dep then
        edges := edges.push { source := name.toString, target := dep.toString }

  IO.eprintln s!"Extracted {edges.size} edges"

  -- Output JSON to stdout
  let graphData : GraphData := { nodes := nodes, edges := edges }
  IO.println (toJson graphData)
