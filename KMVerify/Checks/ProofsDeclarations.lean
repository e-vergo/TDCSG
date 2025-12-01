/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import KMVerify.Types
import KMVerify.Config
import KMVerify.FileUtils

/-!
# Proofs Declarations Check

Verify that Proofs/ directory contains only lemmas and theorems.
No defs, instances, structures, classes, etc.
-/

namespace KMVerify.Checks

/-- Check that Proofs/ contains only lemmas and theorems -/
def checkProofsDeclarations (resolved : ResolvedConfig) : IO CheckResult := do
  let files ← collectLeanFiles resolved.proofsPath
  let mut violations : List (String × ParsedDecl) := []

  for file in files do
    let decls ← parseDeclarations file
    let relPath := file.toString.replace (resolved.projectRoot.toString ++ "/") ""
    for decl in decls do
      -- Only lemmas and theorems are allowed in Proofs/
      match decl.kind with
      | .theorem_ => pure ()
      | .lemma_ => pure ()
      | _ => violations := violations ++ [(relPath, decl)]

  if violations.isEmpty then
    return CheckResult.pass "Proofs Declarations"
      s!"Proofs/ contains only lemmas and theorems ({files.length} files)"
  else
    let details := violations.map fun (file, decl) =>
      s!"{file}:{decl.line} - {decl.kind} {decl.name}"
    return CheckResult.fail "Proofs Declarations"
      s!"{violations.length} non-lemma/theorem declarations in Proofs/" details

end KMVerify.Checks
