/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import KMVerify.Types
import KMVerify.Config

/-!
# Transparency Check

Verify no custom axioms or opaque declarations in the project.
-/

namespace KMVerify.Checks

open Lean Meta

/-- Verify transparency: no custom axioms or opaque declarations -/
def checkTransparency (resolved : ResolvedConfig) : MetaM CheckResult := do
  let env ← getEnv
  let projectPrefix := resolved.config.projectPrefix

  let mut customAxioms : List Name := []
  let mut opaqueDecls : List Name := []

  for (name, info) in env.constants.toList do
    let nameStr := name.toString
    -- Only check project declarations
    if !nameStr.startsWith projectPrefix then
      continue

    match info with
    | .axiomInfo _ =>
      if !isStandardAxiom name && name != ``sorryAx then
        customAxioms := name :: customAxioms
    | .opaqueInfo _ =>
      opaqueDecls := name :: opaqueDecls
    | _ => continue

  let mut details : List String := []
  let mut passed := true

  if !customAxioms.isEmpty then
    passed := false
    details := details ++ customAxioms.map (s!"Custom axiom: {·}")

  if !opaqueDecls.isEmpty then
    -- Opaque declarations are a warning, not a failure
    details := details ++ opaqueDecls.map (s!"Opaque declaration: {·}")

  if customAxioms.isEmpty then
    if opaqueDecls.isEmpty then
      return CheckResult.pass "Transparency"
        "No custom axioms or opaque declarations"
    else
      -- Pass with warning about opaques
      return { CheckResult.pass "Transparency"
        s!"No custom axioms ({opaqueDecls.length} opaque declarations)"
        with details := details }
  else
    return CheckResult.fail "Transparency"
      "Custom axioms detected" details

end KMVerify.Checks
