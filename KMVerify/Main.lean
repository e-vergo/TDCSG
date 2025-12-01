/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import KMVerify.Types
import KMVerify.Config
import KMVerify.FileUtils
import KMVerify.Report
import KMVerify.Checks.Structure
import KMVerify.Checks.Axioms
import KMVerify.Checks.Transparency
import KMVerify.Checks.Completeness
import KMVerify.Checks.ProofMinimality
import KMVerify.Checks.Duplicates
import KMVerify.Checks.Imports
import KMVerify.Checks.MainTheoremPurity
import KMVerify.Checks.Instances
import KMVerify.Checks.TrivialDefs
import KMVerify.Checks.ProofsDeclarations

/-!
# KMVerify Main

CLI entry point and orchestration for Kim Morrison Standard verification.

## Usage

```bash
lake env lean --run KMVerify/Main.lean [project_root] [--json]
```

If project_root is not provided, uses current directory.
-/

namespace KMVerify

open Lean Meta

/-! ## Statistics Collection -/

/-- Collect project statistics -/
def collectStats (resolved : ResolvedConfig) : IO ProjectStats := do
  -- MathlibExtensions
  let mathlibExtStats ← do
    match resolved.mathlibExtensionsPath with
    | none => pure none
    | some path =>
      let files ← collectLeanFiles path
      let lines ← countTotalLines files
      pure (some { fileCount := files.length, lineCount := lines })

  -- Definitions
  let defFiles ← collectLeanFiles resolved.definitionsPath
  let defLines ← countTotalLines defFiles
  let defStats : TierStats := { fileCount := defFiles.length, lineCount := defLines }

  -- Proofs
  let proofFiles ← collectLeanFiles resolved.proofsPath
  let proofLines ← countTotalLines proofFiles
  let proofStats : TierStats := { fileCount := proofFiles.length, lineCount := proofLines }

  -- MainTheorem
  let mainLines ← countLines resolved.mainTheoremPath
  let mainStats : TierStats := { fileCount := 1, lineCount := mainLines }

  -- ProofOfMainTheorem
  let proofOfMainLines ← countLines resolved.proofOfMainTheoremPath
  let proofOfMainStats : TierStats := { fileCount := 1, lineCount := proofOfMainLines }

  return {
    mathlibExtensions := mathlibExtStats
    definitions := defStats
    proofs := proofStats
    mainTheorem := mainStats
    proofOfMainTheorem := proofOfMainStats
  }

/-! ## Check Orchestration -/

/-- Run all IO-based checks (no MetaM required) -/
def runIOChecks (resolved : ResolvedConfig) : IO (List CheckResult) := do
  let completeness ← Checks.checkCompleteness resolved
  let proofMinimality ← Checks.checkProofMinimality resolved
  let duplicates ← Checks.checkDuplicates resolved
  let imports ← Checks.checkImports resolved
  let mainPurity ← Checks.checkMainTheoremPurity resolved
  let instances ← Checks.checkInstances resolved
  let trivialDefs ← Checks.checkTrivialDefs resolved
  let proofsDecls ← Checks.checkProofsDeclarations resolved

  return [completeness, proofMinimality, duplicates, imports, mainPurity, instances, trivialDefs, proofsDecls]

/-- Run all MetaM-based checks -/
def runMetaChecks (resolved : ResolvedConfig) : MetaM (List CheckResult) := do
  let structure_ ← Checks.checkStructure resolved
  let axioms ← Checks.checkAxioms resolved
  let transparency ← Checks.checkTransparency resolved

  return [structure_, axioms, transparency]

/-- Run all checks and build report -/
def runVerification (resolved : ResolvedConfig) : MetaM VerificationReport := do
  -- Run IO checks
  let ioChecks ← runIOChecks resolved

  -- Run Meta checks
  let metaChecks ← runMetaChecks resolved

  -- Combine in display order
  let allChecks := metaChecks ++ ioChecks

  -- Collect stats
  let stats ← collectStats resolved

  -- Check if all passed
  let allPassed := allChecks.all (·.passed)

  return {
    projectName := resolved.config.projectPrefix
    checks := allChecks
    stats := stats
    allPassed := allPassed
  }

/-! ## CLI Entry Point -/

/-- Parse command line arguments -/
def parseArgs (args : List String) : IO (System.FilePath × Bool) := do
  let mut projectRoot : System.FilePath := "."
  let mut jsonMode := false

  for arg in args do
    if arg == "--json" then
      jsonMode := true
    else if !arg.startsWith "-" then
      projectRoot := arg

  return (projectRoot, jsonMode)

/-- Main entry point -/
def main (args : List String) : IO UInt32 := do
  let (projectRoot, jsonMode) ← parseArgs args

  -- Load and resolve configuration
  match ← loadAndResolveConfig projectRoot with
  | .error e =>
    IO.eprintln s!"Error: {e}"
    return (1 : UInt32)
  | .ok resolved =>
    -- Build the project module to get access to environment
    let proofModule := s!"{resolved.config.projectPrefix}.ProofOfMainTheorem"
    let imports : Array Lean.Import := #[{ module := proofModule.toName }]

    try
      let env ← Lean.importModules imports {}

      let (report, _) ← Lean.Core.CoreM.toIO
        (ctx := { fileName := "KMVerify", fileMap := default, options := {} })
        (s := { env })
        (Lean.Meta.MetaM.run' (runVerification resolved))

      printReport report jsonMode

      return if report.allPassed then (0 : UInt32) else (1 : UInt32)
    catch e =>
      IO.eprintln s!"Error loading project: {e}"
      IO.eprintln "Make sure to run 'lake build' first."
      return (1 : UInt32)

end KMVerify

/-- Entry point when run with `lean --run` -/
def main (args : List String) : IO UInt32 :=
  KMVerify.main args
