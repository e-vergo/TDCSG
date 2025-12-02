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

  -- Find duplicates, excluding MainTheorem re-exports
  let mut duplicates : List (String × List String) := []
  for (name, locations) in definitions.toList do
    if locations.length > 1 then
      -- Check if this is a MainTheorem re-export of a Definitions item
      let hasMainTheorem := locations.any (·.endsWith "MainTheorem.lean")
      let hasDefinitions := locations.any (fun loc =>
        containsSubstr loc ("/" ++ resolved.config.definitionsDir ++ "/"))

      -- If it's a MainTheorem + Definitions pair, check if it's a re-export
      if hasMainTheorem && hasDefinitions && locations.length == 2 then
        -- Find the MainTheorem file and parse the declaration
        let mainTheoremFile := allFiles.find? (·.toString.endsWith "MainTheorem.lean")
        match mainTheoremFile with
        | some mtFile =>
          let mtDecls ← parseDeclarations mtFile
          let mtDecl := mtDecls.find? (·.name == name)
          -- If MainTheorem has an abbrev, it's a re-export, not a duplicate
          match mtDecl with
          | some d =>
            if d.kind == DeclKind.abbrev_ then
              continue  -- Skip this re-export
            else
              duplicates := (name, locations) :: duplicates
          | none =>
            duplicates := (name, locations) :: duplicates
        | none =>
          duplicates := (name, locations) :: duplicates
      else
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
