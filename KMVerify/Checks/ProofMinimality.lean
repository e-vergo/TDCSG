/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import KMVerify.Types
import KMVerify.Config
import KMVerify.FileUtils

/-!
# Proof Minimality Check

Verify ProofOfMainTheorem.lean contains exactly one theorem.
-/

namespace KMVerify.Checks

/-- Verify proof file contains exactly one theorem -/
def checkProofMinimality (resolved : ResolvedConfig) : IO CheckResult := do
  let decls ← parseDeclarations resolved.proofOfMainTheoremPath

  -- Find all theorem declarations
  let theorems := decls.filter (fun d => d.kind == .theorem_ || d.kind == .lemma_)

  -- Find other declarations (excluding theorems)
  let otherDecls := decls.filter (fun d => d.kind != .theorem_ && d.kind != .lemma_)

  let mut details : List String := []
  let mut passed := true

  -- Check theorem count
  if theorems.length == 0 then
    passed := false
    details := details ++ ["No theorem found in ProofOfMainTheorem.lean"]
  else if theorems.length == 1 then
    let thm := theorems.head!
    let expectedName := resolved.config.theoremName
    if thm.name != expectedName then
      details := details ++ [s!"Found theorem '{thm.name}' (expected '{expectedName}')"]
      -- This is a warning, not a failure
  else
    passed := false
    details := details ++ [s!"Multiple theorems found ({theorems.length}):"]
    for thm in theorems do
      details := details ++ [s!"  - {thm.name} (line {thm.line})"]

  -- Check for other declarations
  if !otherDecls.isEmpty then
    passed := false
    details := details ++ [s!"Extra declarations found ({otherDecls.length}):"]
    for decl in otherDecls do
      details := details ++ [s!"  - {decl.kind} {decl.name} (line {decl.line})"]

  if passed then
    let thmName := if theorems.isEmpty then "none" else theorems.head!.name
    return CheckResult.pass "Proof Minimality"
      s!"Contains exactly one theorem: {thmName}"
  else
    return CheckResult.fail "Proof Minimality"
      "ProofOfMainTheorem.lean structure invalid" details

end KMVerify.Checks
