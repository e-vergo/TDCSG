/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import KMVerify.Types
import KMVerify.Config

/-!
# KMVerify Report Formatting

Human-readable and JSON output formatting.
-/

namespace KMVerify

open Lean

/-! ## Constants -/

private def lineWidth : Nat := 80
private def divider : String := String.ofList (List.replicate lineWidth '=')
private def thinDivider : String := String.ofList (List.replicate lineWidth '-')

/-! ## Formatting Helpers -/

/-- Pad a string to a given width -/
private def padRight (s : String) (width : Nat) : String :=
  s ++ String.ofList (List.replicate (width - min s.length width) ' ')

/-- Format a number with thousands separator (simple version) -/
private def formatNumber (n : Nat) : String :=
  toString n

/-! ## Human-Readable Output -/

/-- Format the header -/
def formatHeader (projectName : String) : String :=
  s!"{divider}\n" ++
  s!"KIM MORRISON STANDARD VERIFICATION\n" ++
  s!"Project: {projectName}\n" ++
  s!"{divider}\n"

/-- Format trust tier summary -/
def formatTierSummary (stats : ProjectStats) : String :=
  let header := "\nTRUST TIER SUMMARY\n" ++ thinDivider ++ "\n"

  -- MathlibExtensions
  let mathlibLine := match stats.mathlibExtensions with
  | some s =>
    s!"  {padRight "MathlibExtensions/" 28}{padRight (toString s.fileCount ++ " files") 12}{formatNumber s.lineCount} lines\n"
  | none =>
    s!"  {padRight "MathlibExtensions/" 28}[NOT PRESENT]\n"

  -- Definitions
  let defsLine := s!"  {padRight "Definitions/" 28}{padRight (toString stats.definitions.fileCount ++ " files") 12}{formatNumber stats.definitions.lineCount} lines\n"

  -- Proofs
  let proofsLine := s!"  {padRight "Proofs/" 28}{padRight (toString stats.proofs.fileCount ++ " files") 12}{formatNumber stats.proofs.lineCount} lines\n"

  -- MainTheorem
  let mainThmLine := s!"  {padRight "MainTheorem.lean" 40}{formatNumber stats.mainTheorem.lineCount} lines\n"

  -- ProofOfMainTheorem
  let proofLine := s!"  {padRight "ProofOfMainTheorem.lean" 40}{formatNumber stats.proofOfMainTheorem.lineCount} lines\n"

  let separator := thinDivider ++ "\n"

  -- Review burden
  let total := stats.totalLines
  let review := stats.reviewBurden
  let pct := if total > 0 then (review * 100) / total else 0

  let reviewLine := s!"  REVIEW BURDEN: {formatNumber review} lines"
  let reviewDesc := if stats.mathlibExtensions.isSome then
    " (MathlibExtensions + Definitions + MainTheorem)\n"
  else
    " (Definitions + MainTheorem)\n"
  let totalLine := s!"  TOTAL: {formatNumber total} lines ({pct}% requires review)\n"

  header ++ mathlibLine ++ defsLine ++ proofsLine ++ mainThmLine ++ proofLine ++ separator ++ reviewLine ++ reviewDesc ++ totalLine

/-- Format a single check result -/
def formatCheck (result : CheckResult) : String :=
  let status := if result.passed then "[PASS]" else "[FAIL]"
  let line := s!"  {status} {result.name}"

  if result.passed then
    line ++ "\n"
  else
    let detailLines := result.details.map (s!"         " ++ ·)
    line ++ "\n" ++ String.intercalate "\n" detailLines ++
    (if detailLines.isEmpty then "" else "\n")

/-- Format all check results -/
def formatChecks (checks : List CheckResult) : String :=
  let header := "\nCHECKS\n" ++ thinDivider ++ "\n"
  let body := String.intercalate "" (checks.map formatCheck)
  header ++ body

/-- Format the final result -/
def formatResult (allPassed : Bool) : String :=
  let result := if allPassed then
    "\n" ++ divider ++ "\n" ++
    "RESULT: PROJECT VERIFIED\n" ++
    divider ++ "\n"
  else
    "\n" ++ divider ++ "\n" ++
    "RESULT: VERIFICATION FAILED\n" ++
    "Please fix the issues above before requesting review.\n" ++
    divider ++ "\n"
  result

/-- Format a complete verification report -/
def formatReport (report : VerificationReport) : String :=
  formatHeader report.projectName ++
  formatTierSummary report.stats ++
  formatChecks report.checks ++
  formatResult report.allPassed

/-! ## JSON Output -/

/-- Format report as pretty-printed JSON -/
def formatReportJson (report : VerificationReport) : String :=
  toJson report |>.pretty

/-! ## Console Output -/

/-- Print the report to stdout -/
def printReport (report : VerificationReport) (jsonMode : Bool := false) : IO Unit := do
  if jsonMode then
    IO.println (formatReportJson report)
  else
    IO.println (formatReport report)

end KMVerify
