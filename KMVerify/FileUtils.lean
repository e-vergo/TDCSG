/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import KMVerify.Types

/-!
# KMVerify File Utilities

File scanning, import extraction, line counting, and declaration parsing.
-/

namespace KMVerify

/-! ## String Helpers -/

/-- Check if a string contains a substring -/
def containsSubstr (s : String) (sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-! ## File Collection -/

/-- Recursively collect all .lean files from a directory -/
partial def collectLeanFiles (path : System.FilePath) : IO (List System.FilePath) := do
  let pathExists ← path.pathExists
  if !pathExists then return []

  let isDir ← path.isDir
  if !isDir then
    if path.extension == some "lean" then
      return [path]
    else
      return []

  let entries ← path.readDir
  let mut result : List System.FilePath := []
  for entry in entries do
    let subFiles ← collectLeanFiles entry.path
    result := result ++ subFiles
  return result

/-- Count lines in a file -/
def countLines (path : System.FilePath) : IO Nat := do
  try
    let content ← IO.FS.readFile path
    return (content.splitOn "\n").length
  catch _ =>
    return 0

/-- Count total lines across multiple files -/
def countTotalLines (files : List System.FilePath) : IO Nat := do
  let mut total := 0
  for file in files do
    let lines ← countLines file
    total := total + lines
  return total

/-! ## Import Extraction -/

/-- Represents an import statement -/
structure ImportInfo where
  /-- The module name being imported -/
  moduleName : String
  /-- Line number where the import appears -/
  line : Nat
  deriving Repr

/-- Extract all imports from a Lean file -/
def extractImports (path : System.FilePath) : IO (List ImportInfo) := do
  try
    let content ← IO.FS.readFile path
    let lines := content.splitOn "\n"
    let mut imports : List ImportInfo := []
    let mut lineNum := 0

    for line in lines do
      lineNum := lineNum + 1
      let trimmed := line.trim
      if trimmed.startsWith "import " then
        let rest := trimmed.drop 7  -- "import ".length
        let moduleName := rest.takeWhile (fun c => c != ' ' && c != '\n')
        imports := imports ++ [{ moduleName := moduleName.trim, line := lineNum }]

    return imports
  catch _ =>
    return []

/-- Classify an import by its prefix -/
def classifyImport (moduleName : String) (projectPrefix : String)
    (mathlibExtDir : Option String) (defsDir : String) (proofsDir : String)
    : String :=
  if moduleName.startsWith "Mathlib" then "Mathlib"
  else if moduleName.startsWith "Init" then "Init"
  else if moduleName.startsWith "Lean" then "Lean"
  else if moduleName.startsWith "Batteries" then "Batteries"
  else
    -- Check project-specific imports
    let fullPrefix := projectPrefix ++ "."
    if moduleName.startsWith fullPrefix then
      let rest := moduleName.drop fullPrefix.length
      -- Check MathlibExtensions
      match mathlibExtDir with
      | some extDir =>
        if rest.startsWith (extDir ++ ".") || rest == extDir then
          "MathlibExtensions"
        else if rest.startsWith (defsDir ++ ".") || rest == defsDir then
          "Definitions"
        else if rest.startsWith (proofsDir ++ ".") || rest == proofsDir then
          "Proofs"
        else
          "Project"
      | none =>
        if rest.startsWith (defsDir ++ ".") || rest == defsDir then
          "Definitions"
        else if rest.startsWith (proofsDir ++ ".") || rest == proofsDir then
          "Proofs"
        else
          "Project"
    else
      "External"

/-! ## Declaration Parsing -/

/-- Extract declaration name from rest of line -/
private def extractDeclName (rest : String) : String :=
  -- Take characters that are valid in Lean identifiers
  rest.takeWhile (fun c =>
    c.isAlphanum || c == '_' || c == '\'' ||
    c == '₀' || c == '₁' || c == '₂' || c == '₃' || c == '₄' ||
    c == '₅' || c == '₆' || c == '₇' || c == '₈' || c == '₉')

/-- Parse a single line for a declaration -/
private def parseDeclarationLine (line : String) (lineNum : Nat) : Option ParsedDecl :=
  -- Order matters: check longer patterns first
  let patterns : List (String × DeclKind) := [
    ("noncomputable def ", .def_),
    ("noncomputable abbrev ", .abbrev_),
    ("theorem ", .theorem_),
    ("lemma ", .lemma_),
    ("structure ", .structure_),
    ("class ", .class_),
    ("instance ", .instance_),
    ("axiom ", .axiom_),
    ("opaque ", .opaque_),
    ("abbrev ", .abbrev_),
    ("def ", .def_)
  ]

  let rec go : List (String × DeclKind) → Option ParsedDecl
    | [] => none
    | (pat, kind) :: rest =>
      if line.startsWith pat then
        let afterPat := line.drop pat.length
        let name := extractDeclName afterPat
        if name.isEmpty then
          go rest
        else
          -- Check if def uses := by (proof obligation)
          let actualKind := if kind == .def_ && containsSubstr line ":= by" then
            DeclKind.defByProof
          else
            kind
          some { kind := actualKind, name := name, line := lineNum }
      else
        go rest

  go patterns

/-- Parse declarations from a Lean file (text-based, not AST) -/
def parseDeclarations (path : System.FilePath) : IO (List ParsedDecl) := do
  try
    let content ← IO.FS.readFile path
    let lines := content.splitOn "\n"
    let mut decls : List ParsedDecl := []
    let mut lineNum := 0
    let mut inBlockComment := false

    for line in lines do
      lineNum := lineNum + 1
      let trimmed := line.trim

      -- Track block comments
      if trimmed.startsWith "/-" && !trimmed.startsWith "/-!" then
        inBlockComment := true
      if inBlockComment then
        if (trimmed.splitOn "-/").length > 1 then
          inBlockComment := false
        continue

      -- Skip line comments
      if trimmed.startsWith "--" then
        continue

      -- Check for declarations
      match parseDeclarationLine trimmed lineNum with
      | some d => decls := decls ++ [d]
      | none => pure ()

    return decls
  catch _ =>
    return []

/-! ## Instance Detection -/

/-- Check if a file contains any instance declarations -/
def hasInstances (path : System.FilePath) : IO Bool := do
  let decls ← parseDeclarations path
  return decls.any (·.kind == .instance_)

/-- Get all instance declarations from a file -/
def getInstances (path : System.FilePath) : IO (List ParsedDecl) := do
  let decls ← parseDeclarations path
  return decls.filter (·.kind == .instance_)

/-! ## Sorry Detection -/

/-- Check if a file contains sorry statements -/
def hasSorry (path : System.FilePath) : IO Bool := do
  try
    let content ← IO.FS.readFile path
    -- Simple check: does "sorry" appear as a word?
    -- This could have false positives in comments/strings, but is conservative
    return containsSubstr content "sorry"
  catch _ =>
    return false

/-- Find all sorry occurrences in a file with line numbers -/
def findSorries (path : System.FilePath) : IO (List Nat) := do
  try
    let content ← IO.FS.readFile path
    let lines := content.splitOn "\n"
    let mut sorryLines : List Nat := []
    let mut lineNum := 0

    for line in lines do
      lineNum := lineNum + 1
      if containsSubstr line "sorry" then
        sorryLines := sorryLines ++ [lineNum]

    return sorryLines
  catch _ =>
    return []

/-! ## Trivial Definition Detection -/

/-- Patterns for trivially true/false definitions -/
def isTrivialDef (path : System.FilePath) (decl : ParsedDecl) : IO Bool := do
  if decl.kind != .def_ then return false

  try
    let content ← IO.FS.readFile path
    let lines := content.splitOn "\n"

    -- Get the line and a few following lines for multi-line defs
    if decl.line > lines.length then return false

    let startIdx := decl.line - 1
    let endIdx := min (startIdx + 5) lines.length
    let defLines := (lines.toArray[startIdx:endIdx]).toList
    let defText := String.intercalate " " defLines

    -- Check for trivial patterns
    let trivialPatterns := [
      ": Prop := True",
      ": Prop := False",
      ":= True",
      ":= False",
      "∀ _, True",
      "forall _, True"
    ]

    return trivialPatterns.any (fun pat => containsSubstr defText pat)
  catch _ =>
    return false

/-- Find all trivial definitions in a file -/
def findTrivialDefs (path : System.FilePath) : IO (List ParsedDecl) := do
  let decls ← parseDeclarations path
  let mut trivial : List ParsedDecl := []
  for decl in decls do
    let isTrivialResult ← isTrivialDef path decl
    if isTrivialResult then
      trivial := trivial ++ [decl]
  return trivial

end KMVerify
