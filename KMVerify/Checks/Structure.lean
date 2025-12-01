/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import KMVerify.Types
import KMVerify.Config

/-!
# Structure Check

Verify that required declarations exist in the environment.
-/

namespace KMVerify.Checks

open Lean Meta

/-- Verify that StatementOfTheorem and the main theorem exist -/
def checkStructure (resolved : ResolvedConfig) : MetaM CheckResult := do
  let env ← getEnv
  let statementName := resolved.config.statementName.toName
  let theoremName := resolved.config.theoremName.toName

  let mut details : List String := []
  let mut passed := true

  -- Check statement declaration exists
  match env.find? statementName with
  | some _ => pure ()
  | none =>
    passed := false
    details := details ++ [s!"'{statementName}' not found"]

  -- Check main theorem exists
  match env.find? theoremName with
  | some info =>
    -- Verify it's actually a theorem
    match info with
    | .thmInfo _ => pure ()
    | _ =>
      passed := false
      details := details ++ [s!"'{theoremName}' exists but is not a theorem"]
  | none =>
    passed := false
    details := details ++ [s!"'{theoremName}' not found"]

  if passed then
    return CheckResult.pass "Structure"
      s!"{statementName} and {theoremName} exist"
  else
    return CheckResult.fail "Structure"
      "Required declarations missing" details

end KMVerify.Checks
