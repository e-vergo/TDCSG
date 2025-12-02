import TDCSG.ProofOfMainTheorem
import Lean

open Lean System

def main : IO Unit := do
  IO.println "=== Import Graph for TDCSG.ProofOfMainTheorem ==="
  IO.println ""

  -- Get all modules in the current environment
  let imports ← IO.FS.lines (FilePath.mk "TDCSG/ProofOfMainTheorem.lean")

  IO.println "Direct imports from ProofOfMainTheorem.lean:"
  for line in imports do
    let trimmed := line.trim
    if trimmed.startsWith "import " then
      let moduleName := trimmed.drop 7
      IO.println s!"  - {moduleName}"

  IO.println ""
  IO.println "Use the following commands to explore further:"
  IO.println "  find TDCSG -name '*.lean' | xargs grep '^import' | sort -u"
