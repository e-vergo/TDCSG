/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import KMVerify.Types
import KMVerify.Config
import KMVerify.FileUtils

/-!
# Completeness Check

Verify no sorry statements in source files.
-/

namespace KMVerify.Checks

/-- Check all project files for sorry statements -/
def checkCompleteness (resolved : ResolvedConfig) : IO CheckResult := do
  let mut sorryFiles : List String := []

  -- Collect all files to check
  let mut filesToCheck : List System.FilePath := []

  -- Add MathlibExtensions if present
  if let some extPath := resolved.mathlibExtensionsPath then
    let extFiles ← collectLeanFiles extPath
    filesToCheck := filesToCheck ++ extFiles

  -- Add Definitions
  let defFiles ← collectLeanFiles resolved.definitionsPath
  filesToCheck := filesToCheck ++ defFiles

  -- Add Proofs
  let proofFiles ← collectLeanFiles resolved.proofsPath
  filesToCheck := filesToCheck ++ proofFiles

  -- Add MainTheorem and ProofOfMainTheorem
  filesToCheck := filesToCheck ++ [resolved.mainTheoremPath, resolved.proofOfMainTheoremPath]

  -- Check each file
  for file in filesToCheck do
    let hasSorryResult ← hasSorry file
    if hasSorryResult then
      let relPath := file.toString.replace resolved.projectRoot.toString ""
      sorryFiles := sorryFiles ++ [relPath]

  if sorryFiles.isEmpty then
    return CheckResult.pass "Completeness"
      s!"No sorry statements in {filesToCheck.length} files"
  else
    return CheckResult.fail "Completeness"
      s!"{sorryFiles.length} files contain sorry"
      sorryFiles

end KMVerify.Checks
