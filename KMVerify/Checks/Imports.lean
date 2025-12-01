/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import KMVerify.Types
import KMVerify.Config
import KMVerify.FileUtils

/-!
# Import Discipline Check

Verify imports follow trust tier rules. FAILS on violation.
-/

namespace KMVerify.Checks

/-- Violation of import rules -/
structure ImportViolation where
  file : String
  trustLevel : TrustLevel
  importModule : String
  importClass : String
  line : Nat
  deriving Repr

/-- Check imports for a single file -/
def checkFileImports (resolved : ResolvedConfig) (file : System.FilePath)
    : IO (List ImportViolation) := do
  let trustLevel := getTrustLevel resolved file
  let imports ← extractImports file

  let config := resolved.config
  let mut violations : List ImportViolation := []

  for imp in imports do
    let importClass := classifyImport imp.moduleName
      config.projectPrefix
      config.mathlibExtensionsDir
      config.definitionsDir
      config.proofsDir

    if !isImportAllowed resolved trustLevel importClass then
      let relPath := file.toString.replace (resolved.projectRoot.toString ++ "/") ""
      violations := violations ++ [{
        file := relPath
        trustLevel := trustLevel
        importModule := imp.moduleName
        importClass := importClass
        line := imp.line
      }]

  return violations

/-- Check import discipline across all project files -/
def checkImports (resolved : ResolvedConfig) : IO CheckResult := do
  let mut allFiles : List System.FilePath := []

  -- Collect all files by trust tier
  if let some extPath := resolved.mathlibExtensionsPath then
    let files ← collectLeanFiles extPath
    allFiles := allFiles ++ files

  let defFiles ← collectLeanFiles resolved.definitionsPath
  allFiles := allFiles ++ defFiles

  let proofFiles ← collectLeanFiles resolved.proofsPath
  allFiles := allFiles ++ proofFiles

  allFiles := allFiles ++ [resolved.mainTheoremPath, resolved.proofOfMainTheoremPath]

  -- Check each file
  let mut allViolations : List ImportViolation := []
  for file in allFiles do
    let violations ← checkFileImports resolved file
    allViolations := allViolations ++ violations

  if allViolations.isEmpty then
    return CheckResult.pass "Imports"
      s!"All {allFiles.length} files follow import discipline"
  else
    let details := allViolations.map fun v =>
      s!"{v.file}:{v.line} - {v.trustLevel} cannot import {v.importClass} ({v.importModule})"
    return CheckResult.fail "Imports"
      s!"{allViolations.length} import violations" details

end KMVerify.Checks
