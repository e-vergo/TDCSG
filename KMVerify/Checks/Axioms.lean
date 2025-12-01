/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import KMVerify.Types
import KMVerify.Config

/-!
# Axiom Check

Verify that the main theorem uses only standard axioms.
-/

namespace KMVerify.Checks

open Lean Meta

/-- Get all axioms a declaration depends on (recursive traversal) -/
def getAxioms (declName : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let some _ := env.find? declName
    | throwError "Declaration {declName} not found"

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
      let deps := val.value.getUsedConstants
      toVisit := toVisit ++ deps.filter (!visited.contains ·)
    | .thmInfo val =>
      let deps := val.value.getUsedConstants
      toVisit := toVisit ++ deps.filter (!visited.contains ·)
    | _ => continue

  return axioms

/-- Verify axiom usage for the main theorem -/
def checkAxioms (resolved : ResolvedConfig) : MetaM CheckResult := do
  let theoremName := resolved.config.theoremName.toName

  try
    let axioms ← getAxioms theoremName

    if axioms.isEmpty then
      return CheckResult.pass "Axioms" "No axioms used (constructive proof)"

    -- Check for sorryAx (critical failure)
    if axioms.contains ``sorryAx then
      return CheckResult.fail "Axioms"
        "CRITICAL: Proof depends on sorryAx (incomplete proof)"
        ["sorryAx indicates 'sorry' was used in the proof"]

    -- Check for non-standard axioms
    let nonStandard := axioms.filter (!isStandardAxiom ·)

    if !nonStandard.isEmpty then
      let details := nonStandard.toList.map (s!"Non-standard: {·}")
      return CheckResult.fail "Axioms"
        "Non-standard axioms detected" details

    -- All axioms are standard
    let axiomList := axioms.toList.map toString
    return CheckResult.pass "Axioms"
      s!"Uses only standard axioms: {String.intercalate ", " axiomList}"
  catch e =>
    return CheckResult.fail "Axioms"
      s!"Error during axiom verification: {← e.toMessageData.toString}" []

end KMVerify.Checks
