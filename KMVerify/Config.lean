/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import KMVerify.Types
import KMVerify.FileUtils

/-!
# KMVerify Configuration

Parse km_verify.json and build project configuration.
-/

namespace KMVerify

open Lean

/-! ## Configuration Structure -/

/-- Project configuration loaded from km_verify.json -/
structure Config where
  /-- Project name/prefix (e.g., "TDCSG") -/
  projectPrefix : String
  /-- Source directory relative to project root (e.g., "TDCSG") -/
  sourceDir : String
  /-- MathlibExtensions directory name (optional, e.g., "MathlibExtensions") -/
  mathlibExtensionsDir : Option String
  /-- Definitions directory name (e.g., "Definitions") -/
  definitionsDir : String
  /-- Proofs directory name (e.g., "Proofs") -/
  proofsDir : String
  /-- MainTheorem file name (e.g., "MainTheorem.lean") -/
  mainTheoremFile : String
  /-- ProofOfMainTheorem file name (e.g., "ProofOfMainTheorem.lean") -/
  proofOfMainTheoremFile : String
  /-- Statement definition name (e.g., "StatementOfTheorem") -/
  statementName : String
  /-- Main theorem name (e.g., "GG5_infinite_at_critical_radius") -/
  theoremName : String
  deriving Inhabited, Repr

/-! ## Resolved Paths -/

/-- Resolved absolute paths for verification -/
structure ResolvedConfig where
  /-- Base configuration -/
  config : Config
  /-- Absolute project root path -/
  projectRoot : System.FilePath
  /-- Absolute path to source directory -/
  sourcePath : System.FilePath
  /-- Absolute path to MathlibExtensions (if present) -/
  mathlibExtensionsPath : Option System.FilePath
  /-- Absolute path to Definitions directory -/
  definitionsPath : System.FilePath
  /-- Absolute path to Proofs directory -/
  proofsPath : System.FilePath
  /-- Absolute path to MainTheorem.lean -/
  mainTheoremPath : System.FilePath
  /-- Absolute path to ProofOfMainTheorem.lean -/
  proofOfMainTheoremPath : System.FilePath
  deriving Inhabited, Repr

/-! ## JSON Parsing -/

/-- Parse a string field from JSON -/
private def parseString (json : Json) (field : String) : Except String String := do
  match json.getObjValD field with
  | .str s => return s
  | .null => throw s!"Missing required field: {field}"
  | _ => throw s!"Field '{field}' must be a string"

/-- Parse an optional string field from JSON -/
private def parseOptString (json : Json) (field : String) : Option String :=
  match json.getObjValD field with
  | .str s => some s
  | _ => none

/-- Parse Config from JSON -/
def Config.fromJson (json : Json) : Except String Config := do
  let projectPrefix ← parseString json "project_prefix"
  let sourceDir ← parseString json "source_dir"
  let definitionsDir ← parseString json "definitions_dir"
  let proofsDir ← parseString json "proofs_dir"
  let mainTheoremFile ← parseString json "main_theorem_file"
  let proofOfMainTheoremFile ← parseString json "proof_of_main_theorem_file"
  let statementName ← parseString json "statement_name"
  let theoremName ← parseString json "theorem_name"
  let mathlibExtensionsDir := parseOptString json "mathlib_extensions_dir"

  return {
    projectPrefix
    sourceDir
    mathlibExtensionsDir
    definitionsDir
    proofsDir
    mainTheoremFile
    proofOfMainTheoremFile
    statementName
    theoremName
  }

/-! ## Config Loading -/

/-- Load configuration from km_verify.json -/
def loadConfig (projectRoot : System.FilePath) : IO (Except String Config) := do
  let configPath := projectRoot / "km_verify.json"

  let configExists ← configPath.pathExists
  if !configExists then
    return .error s!"Configuration file not found: {configPath}"

  try
    let content ← IO.FS.readFile configPath
    match Json.parse content with
    | .ok json =>
      return Config.fromJson json
    | .error err =>
      return .error s!"Failed to parse km_verify.json: {err}"
  catch e =>
    return .error s!"Failed to read km_verify.json: {e}"

/-! ## Path Resolution -/

/-- Resolve configuration paths to absolute paths -/
def resolveConfig (projectRoot : System.FilePath) (config : Config)
    : IO (Except String ResolvedConfig) := do
  let sourcePath := projectRoot / config.sourceDir

  -- Verify source directory exists
  let sourceExists ← sourcePath.pathExists
  if !sourceExists then
    return .error s!"Source directory not found: {sourcePath}"

  -- Resolve MathlibExtensions path (optional)
  let mathlibExtensionsPath ← do
    match config.mathlibExtensionsDir with
    | none => pure none
    | some dir =>
      let path := sourcePath / dir
      let pathExists ← path.pathExists
      if pathExists then pure (some path) else pure none

  -- Resolve required paths
  let definitionsPath := sourcePath / config.definitionsDir
  let proofsPath := sourcePath / config.proofsDir
  let mainTheoremPath := sourcePath / config.mainTheoremFile
  let proofOfMainTheoremPath := sourcePath / config.proofOfMainTheoremFile

  -- Verify required paths exist
  let defsExists ← definitionsPath.pathExists
  if !defsExists then
    return .error s!"Definitions directory not found: {definitionsPath}"

  let proofsExists ← proofsPath.pathExists
  if !proofsExists then
    return .error s!"Proofs directory not found: {proofsPath}"

  let mainExists ← mainTheoremPath.pathExists
  if !mainExists then
    return .error s!"MainTheorem file not found: {mainTheoremPath}"

  let proofExists ← proofOfMainTheoremPath.pathExists
  if !proofExists then
    return .error s!"ProofOfMainTheorem file not found: {proofOfMainTheoremPath}"

  return .ok {
    config
    projectRoot
    sourcePath
    mathlibExtensionsPath
    definitionsPath
    proofsPath
    mainTheoremPath
    proofOfMainTheoremPath
  }

/-- Load and resolve configuration in one step -/
def loadAndResolveConfig (projectRoot : System.FilePath)
    : IO (Except String ResolvedConfig) := do
  match ← loadConfig projectRoot with
  | .error e => return .error e
  | .ok config => resolveConfig projectRoot config

/-! ## Trust Level Detection -/

/-- Determine trust level for a file path -/
def getTrustLevel (resolved : ResolvedConfig) (path : System.FilePath) : TrustLevel :=
  let pathStr := path.toString

  -- Check MainTheorem
  if pathStr == resolved.mainTheoremPath.toString then
    TrustLevel.MainTheorem
  -- Check ProofOfMainTheorem
  else if pathStr == resolved.proofOfMainTheoremPath.toString then
    TrustLevel.ProofOfMainTheorem
  -- Check MathlibExtensions
  else
    match resolved.mathlibExtensionsPath with
    | some extPath =>
      if pathStr.startsWith extPath.toString then
        TrustLevel.MathlibExtensions
      else if pathStr.startsWith resolved.definitionsPath.toString then
        TrustLevel.Definitions
      else if pathStr.startsWith resolved.proofsPath.toString then
        TrustLevel.Proofs
      else
        TrustLevel.Proofs
    | none =>
      if pathStr.startsWith resolved.definitionsPath.toString then
        TrustLevel.Definitions
      else if pathStr.startsWith resolved.proofsPath.toString then
        TrustLevel.Proofs
      else
        TrustLevel.Proofs

/-! ## Import Validation -/

/-- Check if an import is allowed for a given trust level -/
def isImportAllowed (_resolved : ResolvedConfig) (trustLevel : TrustLevel)
    (importClass : String) : Bool :=
  match trustLevel with
  | .MathlibExtensions =>
    -- Can only import Mathlib, Init, Lean, Batteries, and MathlibExtensions
    importClass == "Mathlib" ||
    importClass == "Init" ||
    importClass == "Lean" ||
    importClass == "Batteries" ||
    importClass == "MathlibExtensions"
  | .Definitions =>
    -- Can import Mathlib, MathlibExtensions, Definitions, and MainTheorem
    -- MainTheorem is allowed so Definitions can provide 5-fold specializations
    importClass == "Mathlib" ||
    importClass == "Init" ||
    importClass == "Lean" ||
    importClass == "Batteries" ||
    importClass == "MathlibExtensions" ||
    importClass == "Definitions" ||
    importClass == "MainTheorem"
  | .Proofs =>
    -- Can import anything
    true
  | .MainTheorem =>
    -- Can import Mathlib, MathlibExtensions, and Definitions (NOT Proofs)
    importClass == "Mathlib" ||
    importClass == "Init" ||
    importClass == "Lean" ||
    importClass == "Batteries" ||
    importClass == "MathlibExtensions" ||
    importClass == "Definitions"
  | .ProofOfMainTheorem =>
    -- Can import anything
    true

/-! ## Declaration Validation -/

/-- Check if a declaration kind is allowed for a given trust level -/
def isDeclAllowed (trustLevel : TrustLevel) (kind : DeclKind) : Bool :=
  match trustLevel with
  | .MathlibExtensions =>
    -- Only def with proof obligation (defByProof), lemmas, theorems
    -- NO: plain def, abbrev, structure, class, instance
    match kind with
    | .defByProof => true
    | .theorem_ => true
    | .lemma_ => true
    | _ => false
  | .Definitions =>
    -- Everything allowed
    true
  | .Proofs =>
    -- Only lemmas and theorems allowed
    -- NO: defs, instances, structures, classes, etc.
    match kind with
    | .theorem_ => true
    | .lemma_ => true
    | _ => false
  | .MainTheorem =>
    -- Only def, abbrev (no lemmas, theorems, instances)
    match kind with
    | .def_ => true
    | .defByProof => true  -- Actually shouldn't have proofs, but allow
    | .abbrev_ => true
    | .structure_ => true
    | .class_ => true
    | .theorem_ => true
    | .lemma_ => true
    | _ => false
  | .ProofOfMainTheorem =>
    -- Only theorem (exactly one)
    kind == .theorem_

end KMVerify
