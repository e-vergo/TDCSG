/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import KMVerify.Types
import KMVerify.Config
import KMVerify.FileUtils

/-!
# MainTheorem Purity Check

Verify MainTheorem.lean contains no lemmas or theorems (only defs).
-/

namespace KMVerify.Checks

/-- Check that MainTheorem.lean contains only definitions -/
def checkMainTheoremPurity (resolved : ResolvedConfig) : IO CheckResult := do
  let decls ← parseDeclarations resolved.mainTheoremPath

  -- Find forbidden declarations (lemmas, theorems, instances)
  let forbidden := decls.filter fun d =>
    d.kind == .theorem_ || d.kind == .lemma_ || d.kind == .instance_

  -- Find the statement definition
  let statementDefs := decls.filter fun d =>
    d.name == resolved.config.statementName

  let mut details : List String := []
  let mut passed := true

  -- Check for forbidden declarations
  if !forbidden.isEmpty then
    passed := false
    for decl in forbidden do
      details := details ++ [s!"{decl.kind} {decl.name} (line {decl.line})"]

  -- Check that StatementOfTheorem exists
  if statementDefs.isEmpty then
    passed := false
    details := details ++ [s!"'{resolved.config.statementName}' not found"]

  if passed then
    let defCount := decls.filter (fun d => d.kind == .def_ || d.kind == .abbrev_)
    return CheckResult.pass "MainTheorem Purity"
      s!"Contains {defCount.length} definitions, no lemmas/theorems"
  else
    return CheckResult.fail "MainTheorem Purity"
      "MainTheorem.lean should contain only definitions" details

end KMVerify.Checks
