/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import KMVerify.Types
import KMVerify.Config
import KMVerify.FileUtils

/-!
# Trivial Definitions Check

Detect trivially true/false definitions that could indicate proof evasion.
-/

namespace KMVerify.Checks

/-- Check for trivial definitions in reviewed files -/
def checkTrivialDefs (resolved : ResolvedConfig) : IO CheckResult := do
  -- Only check files that require human review:
  -- MathlibExtensions, Definitions, and MainTheorem
  let mut filesToCheck : List System.FilePath := []

  if let some extPath := resolved.mathlibExtensionsPath then
    let files ← collectLeanFiles extPath
    filesToCheck := filesToCheck ++ files

  let defFiles ← collectLeanFiles resolved.definitionsPath
  filesToCheck := filesToCheck ++ defFiles

  filesToCheck := filesToCheck ++ [resolved.mainTheoremPath]

  -- Find trivial definitions
  let mut allTrivial : List (String × ParsedDecl) := []

  for file in filesToCheck do
    let trivialDefs ← findTrivialDefs file
    let relPath := file.toString.replace (resolved.projectRoot.toString ++ "/") ""
    for def_ in trivialDefs do
      allTrivial := allTrivial ++ [(relPath, def_)]

  if allTrivial.isEmpty then
    return CheckResult.pass "No Trivial Definitions"
      s!"No trivially true/false definitions in {filesToCheck.length} reviewed files"
  else
    let details := allTrivial.map fun (file, def_) =>
      s!"{file}:{def_.line} - def {def_.name} (trivially true/false)"
    return CheckResult.fail "No Trivial Definitions"
      s!"{allTrivial.length} trivial definitions found" details

end KMVerify.Checks
