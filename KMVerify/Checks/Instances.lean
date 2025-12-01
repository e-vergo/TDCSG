/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import KMVerify.Types
import KMVerify.Config
import KMVerify.FileUtils

/-!
# Instance Check

Verify no instance declarations in MathlibExtensions.
-/

namespace KMVerify.Checks

/-- Check that MathlibExtensions contains no instances -/
def checkInstances (resolved : ResolvedConfig) : IO CheckResult := do
  -- If no MathlibExtensions directory, pass automatically
  let some extPath := resolved.mathlibExtensionsPath
    | return CheckResult.pass "No Instances"
        "MathlibExtensions directory not present"

  let files ← collectLeanFiles extPath
  let mut allInstances : List (String × ParsedDecl) := []

  for file in files do
    let instances ← getInstances file
    let relPath := file.toString.replace (resolved.projectRoot.toString ++ "/") ""
    for inst in instances do
      allInstances := allInstances ++ [(relPath, inst)]

  if allInstances.isEmpty then
    return CheckResult.pass "No Instances"
      s!"No instances in MathlibExtensions ({files.length} files)"
  else
    let details := allInstances.map fun (file, inst) =>
      s!"{file}:{inst.line} - instance {inst.name}"
    return CheckResult.fail "No Instances"
      s!"{allInstances.length} instances found in MathlibExtensions" details

end KMVerify.Checks
