/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import KMVerify.Types
import KMVerify.Config
import KMVerify.FileUtils

/-!
# Duplicates Check

Verify no duplicate definition names across files.
-/

namespace KMVerify.Checks

/-- Check for duplicate definitions across the project -/
def checkDuplicates (resolved : ResolvedConfig) : IO CheckResult := do
  -- Collect all files
  let mut allFiles : List System.FilePath := []

  if let some extPath := resolved.mathlibExtensionsPath then
    let files ← collectLeanFiles extPath
    allFiles := allFiles ++ files

  let defFiles ← collectLeanFiles resolved.definitionsPath
  allFiles := allFiles ++ defFiles

  let proofFiles ← collectLeanFiles resolved.proofsPath
  allFiles := allFiles ++ proofFiles

  allFiles := allFiles ++ [resolved.mainTheoremPath, resolved.proofOfMainTheoremPath]

  -- Track definitions: name -> list of files
  let mut definitions : Std.HashMap String (List String) := {}

  for file in allFiles do
    let decls ← parseDeclarations file
    let relPath := file.toString.replace (resolved.projectRoot.toString ++ "/") ""

    for decl in decls do
      -- Skip private/internal names
      if decl.name.startsWith "_" || decl.name.length < 2 then
        continue

      let existing := definitions.getD decl.name []
      definitions := definitions.insert decl.name (relPath :: existing)

  -- Find duplicates
  let mut duplicates : List (String × List String) := []
  for (name, locations) in definitions.toList do
    if locations.length > 1 then
      duplicates := (name, locations) :: duplicates

  if duplicates.isEmpty then
    return CheckResult.pass "No Duplicates"
      "All definitions have unique names"
  else
    let mut details : List String := []
    for (name, locations) in duplicates do
      details := details ++ [s!"'{name}' defined in: {String.intercalate ", " locations}"]
    return CheckResult.fail "No Duplicates"
      s!"{duplicates.length} duplicate definitions found" details

end KMVerify.Checks
