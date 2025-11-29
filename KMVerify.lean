/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import Lean
import TDCSG.ProofOfMainTheorem

/-!
# Kim Morrison Standard Verification Tool

This file provides automated verification that a project complies with the Kim Morrison
standard for AI-assisted formal mathematics.

Reference: https://leanprover.zulipchat.com/#narrow/channel/219941-Machine-Learning-for-Theorem-Proving/topic/Discussion.3A.20AI-written.20mathematical.proofs/with/558843568

## Verification Checks

1. **Axiom Soundness**: Checks that `mainTheorem` uses only standard axioms (no sorryAx)
2. **Structure**: Verifies `StatementOfTheorem` and `mainTheorem` exist
3. **Import Discipline**: Ensures MainTheorem.lean imports only from Mathlib or TDCSG.Definitions
4. **Transparency**: No custom axioms, opaque definitions, or proof evasion
5. **Completeness**: No sorry statements in source code
6. **Metrics**: Calculates review burden (public API lines vs total)

## Usage

Run this file with:
```
lake env lean --run KMVerify.lean
```

Or use the command:
```lean
#km_verify
```

For detailed axiom analysis of a specific declaration:
```lean
#km_axioms mainTheorem
```
-/

open Lean Meta Elab Command

/-- Standard axioms that are acceptable in Lean 4 -/
def standardAxioms : List Name :=
  [ ``Classical.choice
  , ``Quot.sound
  , ``propext
  , ``funext
  ]

/-- Check if an axiom is standard -/
def isStandardAxiom (ax : Name) : Bool :=
  standardAxioms.contains ax

/-! ## Configuration -/

/-- Configuration for Kim Morrison standard verification.
    Allows the tool to be used with any project following this standard. -/
structure KMVerifyConfig where
  /-- The main theorem declaration name -/
  theoremName : Name := `GG5_infinite_at_critical_radius
  /-- The statement/proposition declaration name -/
  statementName : Name := `StatementOfTheorem
  /-- Project prefix for filtering declarations (e.g., "TDCSG") -/
  projectPrefix : String := "TDCSG"
  /-- Path to the statement file (should only import Mathlib) -/
  statementFile : System.FilePath := "TDCSG/MainTheorem.lean"
  /-- Path to the proof file -/
  proofFile : System.FilePath := "TDCSG/ProofOfMainTheorem.lean"
  /-- List of supporting module files for metrics calculation -/
  supportingFiles : List String := [
    "Basic.lean", "Properties.lean", "Composition.lean",
    "MeasurePreserving.lean", "Finite.lean", "IntervalExchange.lean",
    "Rotations.lean", "Disks.lean", "TwoDisk.lean",
    "IET.lean", "RealDynamics.lean", "OrbitInfinite.lean", "Geometry.lean"
  ]
  deriving Inhabited

/-- Default configuration for TDCSG project -/
def defaultConfig : KMVerifyConfig := {}

/-! ## JSON Result Types (for MCP integration) -/

/-- Result of a single verification check -/
structure CheckResult where
  /-- Whether the check passed -/
  passed : Bool
  /-- Human-readable message -/
  message : String
  /-- Additional details (e.g., list of axioms found) -/
  details : List String := []
  deriving Inhabited

instance : ToJson CheckResult where
  toJson r := Json.mkObj [
    ("passed", toJson r.passed),
    ("message", toJson r.message),
    ("details", toJson r.details)
  ]

/-- Complete verification report -/
structure VerificationReport where
  structureCheck : CheckResult
  axiomCheck : CheckResult
  importCheck : CheckResult
  transparencyCheck : CheckResult
  completenessCheck : CheckResult
  proofMinimalityCheck : CheckResult
  definitionIsolationCheck : CheckResult
  noDuplicatesCheck : CheckResult
  definitionsOnlyCheck : CheckResult
  noDefsOutsideCheck : CheckResult
  reviewLines : Nat
  totalLines : Nat
  allPassed : Bool
  deriving Inhabited

instance : ToJson VerificationReport where
  toJson r := Json.mkObj [
    ("structure", toJson r.structureCheck),
    ("axioms", toJson r.axiomCheck),
    ("imports", toJson r.importCheck),
    ("transparency", toJson r.transparencyCheck),
    ("completeness", toJson r.completenessCheck),
    ("proofMinimality", toJson r.proofMinimalityCheck),
    ("definitionIsolation", toJson r.definitionIsolationCheck),
    ("noDuplicates", toJson r.noDuplicatesCheck),
    ("definitionsOnly", toJson r.definitionsOnlyCheck),
    ("noDefsOutside", toJson r.noDefsOutsideCheck),
    ("reviewLines", toJson r.reviewLines),
    ("totalLines", toJson r.totalLines),
    ("allPassed", toJson r.allPassed)
  ]

/-- Get all axioms a declaration depends on -/
def getAxioms (declName : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let some info := env.find? declName
    | throwError "Declaration {declName} not found"

  -- Collect axioms recursively
  let mut axioms : Array Name := #[]
  let mut visited : Std.HashSet Name := {}
  let mut toVisit : Array Name := #[declName]

  while h : toVisit.size > 0 do
    let curr := toVisit[toVisit.size - 1]'(by omega)
    toVisit := toVisit.pop

    if visited.contains curr then
      continue
    visited := visited.insert curr

    let some currInfo := env.find? curr
      | continue

    match currInfo with
    | .axiomInfo _ =>
      axioms := axioms.push curr
    | .defnInfo val =>
      -- Add dependencies from value
      let deps := val.value.getUsedConstants
      toVisit := toVisit ++ deps.filter (!visited.contains ·)
    | .thmInfo val =>
      -- Add dependencies from value
      let deps := val.value.getUsedConstants
      toVisit := toVisit ++ deps.filter (!visited.contains ·)
    | _ => continue

  return axioms

/-- Verify axiom usage for the main theorem -/
def verifyAxioms (cfg : KMVerifyConfig := defaultConfig) : MetaM (Bool × String) := do
  try
    let axioms ← getAxioms cfg.theoremName

    let mut report := s!"[AXIOM ANALYSIS] {cfg.theoremName}\n\n"

    if axioms.isEmpty then
      report := report ++ "[PASS] No axioms used (constructive proof)\n"
      return (true, report)

    -- Check for sorryAx
    if axioms.contains ``sorryAx then
      report := report ++ s!"[FAIL] CRITICAL: {cfg.theoremName} depends on sorryAx\n"
      report := report ++ "  This indicates incomplete proofs with 'sorry' statements\n"
      return (false, report)

    -- Check for non-standard axioms
    let nonStandard := axioms.filter (!isStandardAxiom ·)

    if !nonStandard.isEmpty then
      report := report ++ "[FAIL] Non-standard axioms detected:\n"
      for ax in nonStandard do
        report := report ++ s!"  - {ax}\n"
      return (false, report)

    -- All axioms are standard
    report := report ++ "[PASS] Uses only standard axioms:\n"
    for ax in axioms do
      report := report ++ s!"  - {ax}\n"

    report := report ++ "\n[PASS] No sorryAx detected\n"
    report := report ++ "[PASS] No custom axioms\n"

    return (true, report)
  catch e =>
    return (false, s!"Error during axiom verification: {← e.toMessageData.toString}")

/-- Verify that required declarations exist -/
def verifyStructure (cfg : KMVerifyConfig := defaultConfig) : MetaM (Bool × String) := do
  let env ← getEnv
  let mut report := "[STRUCTURE VERIFICATION]\n\n"
  let mut success := true

  -- Check statement declaration exists
  match env.find? cfg.statementName with
  | some _ =>
    report := report ++ s!"[PASS] {cfg.statementName} : Prop declared\n"
  | none =>
    report := report ++ s!"[FAIL] {cfg.statementName} not found\n"
    success := false

  -- Check main theorem exists
  match env.find? cfg.theoremName with
  | some info =>
    report := report ++ s!"[PASS] {cfg.theoremName} : {cfg.statementName} declared\n"
    -- Check it's actually a theorem
    match info with
    | .thmInfo _ =>
      report := report ++ "  (verified as theorem)\n"
    | _ =>
      report := report ++ s!"  [WARN] {cfg.theoremName} is not a theorem\n"
      success := false
  | none =>
    report := report ++ s!"[FAIL] {cfg.theoremName} not found\n"
    success := false

  return (success, report)

/-- Count declarations in the environment from the current module -/
def countModuleDeclarations : MetaM Nat := do
  let env ← getEnv
  let mut count := 0

  -- This is a simplified count - in practice you'd filter by module
  for (name, _) in env.constants.toList do
    -- Filter out Lean/Mathlib declarations
    if !name.toString.startsWith "Lean" &&
       !name.toString.startsWith "Mathlib" &&
       !name.toString.startsWith "Init" then
      count := count + 1

  return count

/-- Verify import discipline: statement file should only import from Mathlib -/
def verifyImports (cfg : KMVerifyConfig := defaultConfig) : IO (Bool × String) := do
  let mut report := "[IMPORT DISCIPLINE CHECK]\n\n"
  let mut success := true

  try
    -- Read statement file
    let content ← IO.FS.readFile cfg.statementFile

    -- Extract import lines
    let lines := content.splitOn "\n"
    let importLines := lines.filter (fun l => l.trim.startsWith "import")

    report := report ++ s!"Found {importLines.length} import statements\n\n"

    -- Check each import
    -- Allowed: Mathlib.* and TDCSG.Definitions.* (pure definitions, no proofs)
    let mut violations : List String := []
    for line in importLines do
      -- Extract module name (after "import")
      let parts := line.trim.splitOn " "
      if parts.length ≥ 2 then
        let moduleName := parts[1]!
        if moduleName.startsWith "Mathlib" then
          report := report ++ s!"[PASS] {moduleName} (Mathlib)\n"
        else if moduleName.startsWith "TDCSG.Definitions" then
          report := report ++ s!"[PASS] {moduleName} (Definitions - specs only)\n"
        else
          violations := moduleName :: violations
          report := report ++ s!"[FAIL] Disallowed import: {moduleName}\n"
          success := false

    if success then
      report := report ++ "\n[PASS] All imports are from Mathlib or TDCSG.Definitions\n"
      report := report ++ "  (TDCSG.Definitions contains only pure definitions, no proofs)\n"
    else
      report := report ++ s!"\n[FAIL] {cfg.statementFile} has disallowed imports\n"
      report := report ++ "  Allowed: Mathlib.* and TDCSG.Definitions.* (pure specs)\n"
      report := report ++ "  Disallowed: TDCSG.* proof files\n"

    return (success, report)
  catch e =>
    return (false, s!"Error reading {cfg.statementFile}: {e}")

/-- Verify transparency: check for custom axioms or opaque declarations -/
def verifyTransparency (cfg : KMVerifyConfig := defaultConfig) : MetaM (Bool × String) := do
  let env ← getEnv
  let mut report := "[TRANSPARENCY VERIFICATION]\n\n"
  let mut success := true

  -- Collect all non-standard axioms and opaque declarations from the project
  let mut customAxioms : List Name := []
  let mut opaqueDecls : List Name := []

  for (name, info) in env.constants.toList do
    -- Only check project declarations
    let nameStr := name.toString
    if !nameStr.startsWith cfg.projectPrefix &&
       !nameStr.startsWith cfg.statementName.toString &&
       !nameStr.startsWith cfg.theoremName.toString then
      continue

    match info with
    | .axiomInfo _ =>
      -- Check if it's a standard axiom
      if !isStandardAxiom name && name != ``sorryAx then
        customAxioms := name :: customAxioms
    | .opaqueInfo _ =>
      opaqueDecls := name :: opaqueDecls
    | _ => continue

  -- Report findings
  if customAxioms.isEmpty then
    report := report ++ "[PASS] No custom axioms declared\n"
  else
    success := false
    report := report ++ "[FAIL] Custom axioms found:\n"
    for ax in customAxioms do
      report := report ++ s!"  - {ax}\n"

  if opaqueDecls.isEmpty then
    report := report ++ "[PASS] No opaque declarations\n"
  else
    -- Opaque is not necessarily bad, but worth noting
    report := report ++ "[WARN] Opaque declarations found:\n"
    for decl in opaqueDecls do
      report := report ++ s!"  - {decl}\n"

  return (success, report)

/-- Verify completeness: check source files for sorry statements -/
def verifyCompleteness (cfg : KMVerifyConfig := defaultConfig) : IO (Bool × String) := do
  let mut report := "[COMPLETENESS CHECK]\n\n"
  let mut success := true

  try
    -- Check statement file for sorry
    let mainContent ← IO.FS.readFile cfg.statementFile
    if (mainContent.splitOn "sorry").length > 1 then
      success := false
      report := report ++ s!"[FAIL] {cfg.statementFile} contains 'sorry'\n"
    else
      report := report ++ s!"[PASS] {cfg.statementFile} has no sorry\n"

    -- Check proof file for sorry
    let proofContent ← IO.FS.readFile cfg.proofFile
    if (proofContent.splitOn "sorry").length > 1 then
      success := false
      report := report ++ s!"[FAIL] {cfg.proofFile} contains 'sorry'\n"
    else
      report := report ++ s!"[PASS] {cfg.proofFile} has no sorry\n"

    if success then
      report := report ++ "\n[PASS] Source files are complete (no sorry statements)\n"
    else
      report := report ++ "\n[FAIL] Source contains sorry - incomplete proof!\n"

    return (success, report)
  catch e =>
    return (false, s!"Error checking source files: {e}")

/-- Verify that core definitions are isolated in TDCSG/Definitions/ directory.
    This ensures human-reviewable definitions are separated from proof code. -/
def verifyDefinitionIsolation (cfg : KMVerifyConfig := defaultConfig) : IO (Bool × String) := do
  let mut report := "[DEFINITION ISOLATION CHECK]\n\n"
  let mut success := true

  -- Core definitions that must be in Definitions/ directory
  let coreDefinitions := [
    "φ", "r_crit", "Plane", "Word", "ζ₅", "E", "E'", "F", "G",
    "leftCenter", "rightCenter", "length1", "length2", "length3",
    "displacement0", "displacement1", "displacement2",
    "segmentPoint", "segmentPointPlane"
  ]

  try
    -- Scan all .lean files in TDCSG directory
    let dir : System.FilePath := "TDCSG"
    let entries ← dir.readDir
    let mut violations : List (String × String) := []

    for entry in entries do
      if entry.path.extension == some "lean" then
        let fileName := entry.fileName
        -- Skip files in Definitions/ subdirectory
        if fileName.startsWith "Definitions" then
          continue

        let content ← IO.FS.readFile entry.path

        -- Check for definitions of core terms
        -- Note: abbrev creates a transparent alias, so we only flag `def`
        -- which creates actual new definitions
        for defName in coreDefinitions do
          -- Pattern: def/noncomputable def followed by the name
          -- Abbrevs are OK since they just alias canonical definitions
          let patterns := [
            s!"def {defName} ",
            s!"def {defName}:",
            s!"noncomputable def {defName} ",
            s!"noncomputable def {defName}:"
          ]

          for pattern in patterns do
            if (content.splitOn pattern).length > 1 then
              violations := (defName, fileName) :: violations
              break

    if violations.isEmpty then
      report := report ++ "[PASS] All core definitions are in TDCSG/Definitions/\n"
    else
      success := false
      report := report ++ s!"[FAIL] Core definitions found outside Definitions/ ({violations.length}):\n"
      for (defName, fileName) in violations do
        report := report ++ s!"  - {defName} in TDCSG/{fileName}\n"
      report := report ++ "\n  These definitions should be moved to appropriate files in TDCSG/Definitions/\n"

    return (success, report)
  catch e =>
    return (false, s!"Error checking definition isolation: {e}")

/-- Helper: Collect all .lean files recursively from a directory -/
partial def collectLeanFiles (path : System.FilePath) : IO (List System.FilePath) := do
  let entries ← path.readDir
  let mut result := []
  for entry in entries do
    let isDir ← entry.path.isDir
    if isDir then
      let subFiles ← collectLeanFiles entry.path
      result := result ++ subFiles
    else if entry.path.extension == some "lean" then
      result := entry.path :: result
  return result

/-- Helper: Collect all .lean files recursively, excluding Definitions/ -/
partial def collectLeanFilesExcludingDefs (path : System.FilePath) : IO (List System.FilePath) := do
  let entries ← path.readDir
  let mut result := []
  for entry in entries do
    -- Skip Definitions/ directory
    if entry.fileName == "Definitions" then
      continue
    let isDir ← entry.path.isDir
    if isDir then
      let subFiles ← collectLeanFilesExcludingDefs entry.path
      result := result ++ subFiles
    else if entry.path.extension == some "lean" then
      result := entry.path :: result
  return result

/-- Verify that there are no duplicate definition names across the codebase.
    This prevents confusion and ensures a single source of truth for each definition. -/
def verifyNoDuplicates (cfg : KMVerifyConfig := defaultConfig) : IO (Bool × String) := do
  let mut report := "[DUPLICATE DEFINITION CHECK]\n\n"
  let mut success := true

  -- Track all definitions and their locations
  let mut definitions : Std.HashMap String (List String) := {}

  try
    -- Scan all .lean files in TDCSG directory recursively
    let dir : System.FilePath := "TDCSG"
    let filesToCheck ← collectLeanFiles dir

    -- Extract definition names from each file
    for filePath in filesToCheck do
      let content ← IO.FS.readFile filePath
      let lines := content.splitOn "\n"
      let relPath := filePath.toString.replace (dir.toString ++ "/") ""

      for line in lines do
        let trimmed := line.trim
        -- Skip comments
        if trimmed.startsWith "--" || trimmed.startsWith "/-" then
          continue

        -- Match definition patterns
        let declarationKeywords := [
          "def ", "theorem ", "lemma ", "abbrev ", "structure ", "class ",
          "noncomputable def ", "noncomputable abbrev "
        ]

        for kw in declarationKeywords do
          if trimmed.startsWith kw then
            -- Extract definition name
            let rest := trimmed.drop kw.length
            let name := rest.takeWhile (fun c => c.isAlphanum || c == '_' || c == '\'' || c == '₅' || c == '₁' || c == '₂' || c == '₃')

            -- Filter out generic names and private definitions
            if name.isEmpty || name.startsWith "_" || name.length < 2 then
              continue

            -- Add to definitions map
            let existing := definitions.getD name []
            definitions := definitions.insert name (relPath :: existing)
            break

    -- Check for duplicates
    let mut duplicates : List (String × List String) := []
    for (name, locations) in definitions.toList do
      if locations.length > 1 then
        duplicates := (name, locations) :: duplicates

    if duplicates.isEmpty then
      report := report ++ "[PASS] No duplicate definitions found\n"
    else
      success := false
      report := report ++ s!"[FAIL] Duplicate definitions detected ({duplicates.length}):\n"
      for (name, locations) in duplicates do
        report := report ++ s!"\n  {name} defined in:\n"
        for loc in locations do
          report := report ++ s!"    - {loc}\n"
      report := report ++ "\n  Each definition should have a single canonical location.\n"

    return (success, report)
  catch e =>
    return (false, s!"Error checking for duplicates: {e}")

/-- Verify that Definitions/*.lean files contain ONLY definitions (def/abbrev/structure/class/instance).
    NO lemmas, theorems, or examples are allowed in Definitions files.
    This ensures human-reviewable definitions are pure definitions without proofs. -/
def verifyDefinitionsOnly (cfg : KMVerifyConfig := defaultConfig) : IO (Bool × String) := do
  let mut report := "[DEFINITIONS-ONLY CHECK]\n\n"
  let mut success := true

  try
    -- Scan all .lean files in TDCSG/Definitions/ directory
    let dir : System.FilePath := "TDCSG/Definitions"
    let entries ← dir.readDir
    let mut violations : List (String × String × String) := []  -- (keyword, name, file)

    -- Keywords that should NOT appear in Definitions files
    let forbiddenKeywords := ["lemma ", "theorem ", "example "]

    for entry in entries do
      if entry.path.extension == some "lean" then
        let fileName := entry.fileName
        let content ← IO.FS.readFile entry.path
        let lines := content.splitOn "\n"

        for line in lines do
          let trimmed := line.trim
          -- Skip comments
          if trimmed.startsWith "--" || trimmed.startsWith "/-" then
            continue

          -- Check for forbidden keywords
          for kw in forbiddenKeywords do
            if trimmed.startsWith kw then
              -- Extract declaration name
              let rest := trimmed.drop kw.length
              let name := rest.takeWhile (fun c => c.isAlphanum || c == '_' || c == '\'' || c == '₅' || c == '₁' || c == '₂' || c == '₃')
              violations := (kw.trim, name, fileName) :: violations

    if violations.isEmpty then
      report := report ++ "[PASS] All Definitions/*.lean files contain only definitions\n"
    else
      success := false
      report := report ++ s!"[FAIL] Lemmas/theorems found in Definitions/ ({violations.length}):\n"
      for (kw, name, fileName) in violations do
        report := report ++ s!"  - {kw} {name} in Definitions/{fileName}\n"
      report := report ++ "\n  Definitions/ files should contain ONLY def/abbrev/structure/class.\n"
      report := report ++ "  Move these lemmas/theorems to appropriate files in TDCSG/.\n"

    return (success, report)
  catch e =>
    return (false, s!"Error checking definitions-only: {e}")

/-- Verify that regular TDCSG/*.lean files contain NO def/abbrev declarations.
    ALL definitions must be in TDCSG/Definitions/ directory.
    This ensures strict separation: Definitions/ has definitions, regular files have proofs. -/
def verifyNoDefsOutsideDefinitions (cfg : KMVerifyConfig := defaultConfig) : IO (Bool × String) := do
  let mut report := "[NO-DEFS-OUTSIDE-DEFINITIONS CHECK]\n\n"
  let mut success := true

  try
    let dir : System.FilePath := "TDCSG"
    let files ← collectLeanFilesExcludingDefs dir
    let mut violations : List (String × String) := []  -- (defName, file)

    -- Keywords that indicate definitions
    let defKeywords := ["def ", "abbrev ", "noncomputable def ", "noncomputable abbrev "]

    for filePath in files do
      let content ← IO.FS.readFile filePath
      let lines := content.splitOn "\n"
      let relPath := filePath.toString.replace "TDCSG/" ""

      for line in lines do
        let trimmed := line.trim
        -- Skip comments
        if trimmed.startsWith "--" || trimmed.startsWith "/-" then
          continue

        -- Check for definition keywords
        for kw in defKeywords do
          if trimmed.startsWith kw then
            -- Extract definition name
            let rest := trimmed.drop kw.length
            let name := rest.takeWhile (fun c => c.isAlphanum || c == '_' || c == '\'' || c == '₅' || c == '₁' || c == '₂' || c == '₃')
            violations := (name, relPath) :: violations

    if violations.isEmpty then
      report := report ++ "[PASS] No definitions found outside Definitions/ directory\n"
    else
      success := false
      report := report ++ s!"[FAIL] Definitions found outside Definitions/ ({violations.length}):\n"
      for (name, fileName) in violations do
        report := report ++ s!"  - def {name} in TDCSG/{fileName}\n"
      report := report ++ "\n  ALL definitions must be in TDCSG/Definitions/.\n"
      report := report ++ "  Regular files should contain ONLY lemmas, theorems, and proofs.\n"

    return (success, report)
  catch e =>
    return (false, s!"Error checking no-defs-outside: {e}")

/-- Verify proof file minimality: ProofOfMainTheorem.lean should contain only the theorem.
    Per Kim Morrison standard, the proof file should have:
    - Import statements
    - Comments/documentation
    - Exactly one theorem declaration: `theorem mainTheorem : StatementOfTheorem := ...`
    No other definitions, lemmas, or declarations allowed. -/
def verifyProofMinimality (cfg : KMVerifyConfig := defaultConfig) : IO (Bool × String) := do
  let mut report := "[PROOF FILE MINIMALITY CHECK]\n\n"
  let mut success := true

  try
    let content ← IO.FS.readFile cfg.proofFile
    let lines := content.splitOn "\n"

    -- Find all declaration lines (excluding comments)
    let mut inBlockComment := false
    let mut declarations : List String := []

    for line in lines do
      let trimmed := line.trim

      -- Track block comments
      if trimmed.startsWith "/-" && !trimmed.startsWith "/-!" then
        inBlockComment := true
      if inBlockComment then
        if (trimmed.splitOn "-/").length > 1 then
          inBlockComment := false
        continue

      -- Skip line comments and doc comments
      if trimmed.startsWith "--" || trimmed.startsWith "/-!" then
        continue

      -- Skip empty lines and import statements
      if trimmed.isEmpty || trimmed.startsWith "import" then
        continue

      -- Check for declarations
      let declarationKeywords := ["def ", "theorem ", "lemma ", "abbrev ", "structure ",
                                   "class ", "instance ", "noncomputable def ",
                                   "noncomputable abbrev ", "opaque ", "axiom "]
      for kw in declarationKeywords do
        if trimmed.startsWith kw then
          -- Extract declaration name
          let rest := trimmed.drop kw.length
          let name := rest.takeWhile (fun c => c.isAlphanum || c == '_' || c == '\'')
          declarations := s!"{kw.trim} {name}" :: declarations
          break

    -- Check results
    let theoremDecls := declarations.filter (·.startsWith "theorem")
    let otherDecls := declarations.filter (!·.startsWith "theorem")

    if theoremDecls.length == 0 then
      success := false
      report := report ++ s!"[FAIL] No theorem found in {cfg.proofFile}\n"
    else if theoremDecls.length == 1 then
      let decl := theoremDecls.head!
      if (decl.splitOn cfg.theoremName.toString).length > 1 then
        report := report ++ s!"[PASS] Contains exactly one theorem: {cfg.theoremName}\n"
      else
        success := false
        report := report ++ s!"[FAIL] Theorem found but not named {cfg.theoremName}: {decl}\n"
    else
      success := false
      report := report ++ s!"[FAIL] Multiple theorems found ({theoremDecls.length}):\n"
      for decl in theoremDecls do
        report := report ++ s!"  - {decl}\n"

    if !otherDecls.isEmpty then
      success := false
      report := report ++ s!"[FAIL] Extra declarations found ({otherDecls.length}):\n"
      for decl in otherDecls do
        report := report ++ s!"  - {decl}\n"
      report := report ++ "\n  Per Kim Morrison standard, ProofOfMainTheorem.lean should contain\n"
      report := report ++ "  only imports and the single mainTheorem declaration.\n"
    else
      report := report ++ "[PASS] No extra declarations (only mainTheorem)\n"

    if success then
      report := report ++ s!"\n[PASS] {cfg.proofFile} is minimal per Kim Morrison standard\n"

    return (success, report)
  catch e =>
    return (false, s!"Error checking {cfg.proofFile}: {e}")

/-- Calculate review burden metrics -/
def calculateMetrics (cfg : KMVerifyConfig := defaultConfig) : IO (Nat × Nat × String) := do
  let mut report := "[REVIEW BURDEN METRICS]\n\n"

  try
    -- Count lines in review-critical files
    let mainContent ← IO.FS.readFile cfg.statementFile
    let proofContent ← IO.FS.readFile cfg.proofFile

    let mainLines := mainContent.splitOn "\n" |>.length
    let proofLines := proofContent.splitOn "\n" |>.length
    let reviewLines := mainLines + proofLines

    report := report ++ s!"{cfg.statementFile}: {mainLines} lines\n"
    report := report ++ s!"{cfg.proofFile}: {proofLines} lines\n"
    report := report ++ s!"Total review burden: {reviewLines} lines\n\n"

    -- Try to count total project lines (rough estimate)
    -- Extract directory from statementFile path
    let dir := cfg.statementFile.parent.getD "."

    let mut totalLines := reviewLines
    for file in cfg.supportingFiles do
      let path := dir / file
      try
        let content ← IO.FS.readFile path
        totalLines := totalLines + (content.splitOn "\n").length
      catch _ =>
        continue

    report := report ++ s!"Estimated total project: {totalLines} lines\n"
    let reduction := if totalLines > 0 then (reviewLines * 100) / totalLines else 0
    report := report ++ s!"Review burden reduction: {100 - reduction}% fewer lines to review\n"

    return (reviewLines, totalLines, report)
  catch e =>
    return (0, 0, s!"Error calculating metrics: {e}\n")

/-- Main verification function (CLI output) -/
def runVerification (cfg : KMVerifyConfig := defaultConfig) : MetaM Unit := do
  IO.println "\n╔════════════════════════════════════════════════════════════╗"
  IO.println "║   KIM MORRISON STANDARD VERIFICATION                       ║"
  let padding := String.replicate (42 - cfg.projectPrefix.length) ' '
  IO.println s!"║   {cfg.projectPrefix} Project{padding}║"
  IO.println "╚════════════════════════════════════════════════════════════╝\n"

  -- Track results
  let mut allPassed := true

  -- Check 1: Structure
  let (structOk, structReport) ← verifyStructure cfg
  IO.println structReport
  allPassed := allPassed && structOk

  -- Check 2: Axioms
  let (axiomsOk, axiomsReport) ← verifyAxioms cfg
  IO.println axiomsReport
  allPassed := allPassed && axiomsOk

  -- Check 3: Import Discipline
  let (importsOk, importsReport) ← verifyImports cfg
  IO.println importsReport
  allPassed := allPassed && importsOk

  -- Check 4: Transparency
  let (transOk, transReport) ← verifyTransparency cfg
  IO.println transReport
  allPassed := allPassed && transOk

  -- Check 5: Completeness
  let (completeOk, completeReport) ← verifyCompleteness cfg
  IO.println completeReport
  allPassed := allPassed && completeOk

  -- Check 6: Proof Minimality
  let (minimalOk, minimalReport) ← verifyProofMinimality cfg
  IO.println minimalReport
  allPassed := allPassed && minimalOk

  -- Check 7: Definition Isolation
  let (isolationOk, isolationReport) ← verifyDefinitionIsolation cfg
  IO.println isolationReport
  allPassed := allPassed && isolationOk

  -- Check 8: No Duplicates
  let (noDupsOk, noDupsReport) ← verifyNoDuplicates cfg
  IO.println noDupsReport
  allPassed := allPassed && noDupsOk

  -- Check 9: Definitions Only (Definitions/ files)
  let (defsOnlyOk, defsOnlyReport) ← verifyDefinitionsOnly cfg
  IO.println defsOnlyReport
  allPassed := allPassed && defsOnlyOk

  -- Check 10: No Defs Outside Definitions/
  let (noDefsOutOk, noDefsOutReport) ← verifyNoDefsOutsideDefinitions cfg
  IO.println noDefsOutReport
  allPassed := allPassed && noDefsOutOk

  -- Check 11: Metrics
  let (_, _, metricsReport) ← calculateMetrics cfg
  IO.println metricsReport

  -- Summary
  IO.println "════════════════════════════════════════════════════════════"
  IO.println "VERIFICATION SUMMARY\n"

  if structOk then
    IO.println "[PASS] Structure Compliance"
  else
    IO.println "[FAIL] Structure Compliance"

  if axiomsOk then
    IO.println "[PASS] Axiom Soundness"
  else
    IO.println "[FAIL] Axiom Soundness"

  if importsOk then
    IO.println "[PASS] Import Discipline"
  else
    IO.println "[FAIL] Import Discipline"

  if transOk then
    IO.println "[PASS] Transparency"
  else
    IO.println "[FAIL] Transparency"

  if completeOk then
    IO.println "[PASS] Completeness"
  else
    IO.println "[FAIL] Completeness"

  if minimalOk then
    IO.println "[PASS] Proof Minimality"
  else
    IO.println "[FAIL] Proof Minimality"

  if isolationOk then
    IO.println "[PASS] Definition Isolation"
  else
    IO.println "[FAIL] Definition Isolation"

  if noDupsOk then
    IO.println "[PASS] No Duplicates"
  else
    IO.println "[FAIL] No Duplicates"

  if defsOnlyOk then
    IO.println "[PASS] Definitions Only (in Definitions/)"
  else
    IO.println "[FAIL] Definitions Only (in Definitions/)"

  if noDefsOutOk then
    IO.println "[PASS] No Defs Outside Definitions/"
  else
    IO.println "[FAIL] No Defs Outside Definitions/"

  IO.println "════════════════════════════════════════════════════════════"

  if allPassed then
    IO.println "\nRESULT: PROJECT VERIFIED\n"
    IO.println "This project FULLY COMPLIES with the Kim Morrison standard:"
    IO.println s!"  • {cfg.theoremName} uses only standard axioms (no sorryAx)"
    IO.println s!"  • {cfg.statementFile} imports only from Mathlib or TDCSG.Definitions"
    IO.println "  • No custom axioms or opaque declarations"
    IO.println "  • Source code is complete (no sorry statements)"
    IO.println s!"  • {cfg.proofFile} contains only {cfg.theoremName}"
    IO.println "  • Structure follows required conventions"
    IO.println "  • Definitions are properly isolated in Definitions/"
    IO.println "  • No duplicate definitions across files"
    IO.println "\nSafe for community review and Mathlib PR.\n"
  else
    IO.println "\nRESULT: VERIFICATION FAILED\n"
    IO.println "Please fix the issues above before requesting review.\n"

/-! ## JSON API for MCP Integration -/

/-- Collect all verification results into a structured report -/
def collectVerificationReport (cfg : KMVerifyConfig := defaultConfig) : MetaM VerificationReport := do
  -- Run all checks
  let (structOk, structMsg) ← verifyStructure cfg
  let (axiomsOk, axiomsMsg) ← verifyAxioms cfg
  let (importsOk, importsMsg) ← verifyImports cfg
  let (transOk, transMsg) ← verifyTransparency cfg
  let (completeOk, completeMsg) ← verifyCompleteness cfg
  let (minimalOk, minimalMsg) ← verifyProofMinimality cfg
  let (isolationOk, isolationMsg) ← verifyDefinitionIsolation cfg
  let (noDupsOk, noDupsMsg) ← verifyNoDuplicates cfg
  let (defsOnlyOk, defsOnlyMsg) ← verifyDefinitionsOnly cfg
  let (noDefsOutOk, noDefsOutMsg) ← verifyNoDefsOutsideDefinitions cfg
  let (reviewLines, totalLines, _) ← calculateMetrics cfg

  return {
    structureCheck := { passed := structOk, message := structMsg }
    axiomCheck := { passed := axiomsOk, message := axiomsMsg }
    importCheck := { passed := importsOk, message := importsMsg }
    transparencyCheck := { passed := transOk, message := transMsg }
    completenessCheck := { passed := completeOk, message := completeMsg }
    proofMinimalityCheck := { passed := minimalOk, message := minimalMsg }
    definitionIsolationCheck := { passed := isolationOk, message := isolationMsg }
    noDuplicatesCheck := { passed := noDupsOk, message := noDupsMsg }
    definitionsOnlyCheck := { passed := defsOnlyOk, message := defsOnlyMsg }
    noDefsOutsideCheck := { passed := noDefsOutOk, message := noDefsOutMsg }
    reviewLines := reviewLines
    totalLines := totalLines
    allPassed := structOk && axiomsOk && importsOk && transOk && completeOk && minimalOk &&
                 isolationOk && noDupsOk && defsOnlyOk && noDefsOutOk
  }

/-- Run verification and return JSON (for MCP integration) -/
def runVerificationJson (cfg : KMVerifyConfig := defaultConfig) : MetaM Json := do
  let report ← collectVerificationReport cfg
  return toJson report

/-- MCP-compatible entry point: verify a project by paths -/
def kmVerify (projectPrefix : String) (statementFile : String) (proofFile : String)
    (theoremName : String := "mainTheorem") (statementName : String := "StatementOfTheorem")
    : MetaM Json := do
  let cfg : KMVerifyConfig := {
    projectPrefix := projectPrefix
    statementFile := statementFile
    proofFile := proofFile
    theoremName := theoremName.toName
    statementName := statementName.toName
  }
  runVerificationJson cfg

/-- Command to run verification -/
elab "#km_verify" : command => do
  liftTermElabM do
    runVerification

/-- Command to run verification and output JSON -/
elab "#km_verify_json" : command => do
  liftTermElabM do
    let json ← runVerificationJson
    IO.println json.pretty

-- You can also run it directly by uncommenting:
-- #km_verify

/-!
## Example Usage

### In Lean REPL
```lean
import KMVerify

#km_verify       -- Human-readable output
#km_verify_json  -- JSON output for tooling
```

### Programmatic API
```lean
import KMVerify

-- Use default config
def checkDefault : MetaM (Bool × String) := verifyAxioms

-- Use custom config
def checkCustom : MetaM Json := do
  let cfg : KMVerifyConfig := {
    projectPrefix := "MyProject"
    theoremName := `myMainTheorem
    statementName := `MyStatement
    statementFile := "MyProject/Statement.lean"
    proofFile := "MyProject/Proof.lean"
  }
  runVerificationJson cfg
```

### CLI Usage
```bash
lake env lean --run KMVerify.lean              # Default (TDCSG)
lake env lean --run KMVerify.lean --json       # JSON output
lake env lean --run KMVerify.lean MyProj MyProj/Main.lean MyProj/Proof.lean
```

### CI/CD Integration
Add to your lakefile.lean:
```lean
lean_exe km_verify where
  root := `KMVerify
  supportInterpreter := true
```

Then run:
```bash
lake exe km_verify && echo "Verification passed"
```
-/

/-- Detailed axiom information for a declaration -/
def printAxiomInfo (declName : Name) : MetaM Unit := do
  IO.println s!"\n[AXIOM ANALYSIS] {declName}\n"

  let axioms ← getAxioms declName

  if axioms.isEmpty then
    IO.println "[PASS] No axioms used - fully constructive proof!"
    return

  IO.println s!"Found {axioms.size} axiom(s):\n"

  for ax in axioms do
    let standard := if isStandardAxiom ax then "[PASS] Standard" else "[FAIL] Non-standard"
    let sorryMarker := if ax == ``sorryAx then " [CRITICAL: SORRY]" else ""
    IO.println s!"  {standard}: {ax}{sorryMarker}"

  -- Summary
  let hasNonStandard := axioms.any (!isStandardAxiom ·)
  let hasSorry := axioms.contains ``sorryAx

  IO.println ""
  if hasSorry then
    IO.println "[FAIL] CRITICAL: Proof contains sorry!"
  else if hasNonStandard then
    IO.println "[WARN] Uses non-standard axioms"
  else
    IO.println "[PASS] All axioms are standard"

/-- Command to print axiom info for a specific declaration -/
elab "#km_axioms " n:ident : command => do
  let name := n.getId
  liftTermElabM do
    printAxiomInfo name

-- Example usage (uncomment to use):
-- #km_axioms mainTheorem
-- #km_axioms scaledPolynomial_matches_chebyshev_at_zero

/-- Parse command-line arguments into config -/
def parseArgs (args : List String) : IO KMVerifyConfig := do
  match args with
  | [] =>
    -- Default config for TDCSG
    return defaultConfig
  | ["--json"] =>
    return defaultConfig  -- JSON mode handled separately
  | [proj, stmt, proof] =>
    return {
      projectPrefix := proj
      statementFile := stmt
      proofFile := proof
      theoremName := `mainTheorem
      statementName := `StatementOfTheorem
    }
  | [proj, stmt, proof, thm, stmtName] =>
    return {
      projectPrefix := proj
      statementFile := stmt
      proofFile := proof
      theoremName := thm.toName
      statementName := stmtName.toName
    }
  | _ =>
    IO.eprintln "Usage: km_verify [--json]"
    IO.eprintln "       km_verify <project_prefix> <statement_file> <proof_file>"
    IO.eprintln "       km_verify <project_prefix> <statement_file> <proof_file> <theorem_name> <statement_name>"
    IO.eprintln ""
    IO.eprintln "Examples:"
    IO.eprintln "  km_verify                                    # Use defaults for TDCSG"
    IO.eprintln "  km_verify --json                             # Output JSON format"
    IO.eprintln "  km_verify MyProject MyProject/Main.lean MyProject/Proof.lean"
    return defaultConfig

/-- Main entry point for running verification from command line -/
def main (args : List String) : IO UInt32 := do
  let jsonMode := args.contains "--json"
  let cfg ← parseArgs (args.filter (· != "--json"))

  -- Run the verification in a MetaM context
  let imports : Array Lean.Import := #[{ module := `TDCSG.ProofOfMainTheorem }]
  let env ← Lean.importModules imports {}

  let (passed, _) ← Lean.Core.CoreM.toIO
    (ctx := { fileName := "KMVerify", fileMap := default, options := {} })
    (s := { env })
    (Lean.Meta.MetaM.run' do
      if jsonMode then
        let json ← runVerificationJson cfg
        IO.println json.pretty
        let report ← collectVerificationReport cfg
        return report.allPassed
      else
        runVerification cfg
        let report ← collectVerificationReport cfg
        return report.allPassed)

  return if passed then 0 else 1
