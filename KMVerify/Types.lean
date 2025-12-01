/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import Lean

/-!
# KMVerify Types

Core types for Kim Morrison Standard verification.
-/

namespace KMVerify

open Lean

/-! ## Trust Levels -/

/-- Trust tiers for the Kim Morrison Standard.
Each tier has different import and declaration rules. -/
inductive TrustLevel where
  /-- Highest trust: imports Mathlib only, no instances, defs must have proof obligations -/
  | MathlibExtensions
  /-- Human-reviewed: definitions and supporting lemmas -/
  | Definitions
  /-- Machine-verified: unrestricted -/
  | Proofs
  /-- Statement file: restricted imports, only StatementOfTheorem def -/
  | MainTheorem
  /-- Proof file: unrestricted imports, exactly one theorem -/
  | ProofOfMainTheorem
  deriving DecidableEq, Repr, Inhabited

instance : ToString TrustLevel where
  toString
    | .MathlibExtensions => "MathlibExtensions"
    | .Definitions => "Definitions"
    | .Proofs => "Proofs"
    | .MainTheorem => "MainTheorem"
    | .ProofOfMainTheorem => "ProofOfMainTheorem"

/-! ## Check Results -/

/-- Result of a single verification check -/
structure CheckResult where
  /-- Name of the check -/
  name : String
  /-- Whether the check passed -/
  passed : Bool
  /-- Human-readable message -/
  message : String
  /-- Additional details (e.g., list of violations) -/
  details : List String := []
  deriving Inhabited, Repr

instance : ToJson CheckResult where
  toJson r := Json.mkObj [
    ("name", toJson r.name),
    ("passed", toJson r.passed),
    ("message", toJson r.message),
    ("details", toJson r.details)
  ]

/-- Create a passing check result -/
def CheckResult.pass (name : String) (message : String) : CheckResult :=
  { name, passed := true, message, details := [] }

/-- Create a failing check result -/
def CheckResult.fail (name : String) (message : String) (details : List String := []) : CheckResult :=
  { name, passed := false, message, details }

/-! ## Line Count Statistics -/

/-- Line counts for a trust tier -/
structure TierStats where
  /-- Number of files in this tier -/
  fileCount : Nat
  /-- Total lines of code -/
  lineCount : Nat
  deriving Inhabited, Repr

instance : ToJson TierStats where
  toJson s := Json.mkObj [
    ("file_count", toJson s.fileCount),
    ("line_count", toJson s.lineCount)
  ]

/-- Aggregated statistics across all trust tiers -/
structure ProjectStats where
  mathlibExtensions : Option TierStats
  definitions : TierStats
  proofs : TierStats
  mainTheorem : TierStats
  proofOfMainTheorem : TierStats
  deriving Inhabited, Repr

/-- Calculate total lines in the project -/
def ProjectStats.totalLines (s : ProjectStats) : Nat :=
  (s.mathlibExtensions.map (·.lineCount)).getD 0 +
  s.definitions.lineCount +
  s.proofs.lineCount +
  s.mainTheorem.lineCount +
  s.proofOfMainTheorem.lineCount

/-- Calculate review burden (lines requiring human review) -/
def ProjectStats.reviewBurden (s : ProjectStats) : Nat :=
  (s.mathlibExtensions.map (·.lineCount)).getD 0 +
  s.definitions.lineCount +
  s.mainTheorem.lineCount

instance : ToJson ProjectStats where
  toJson s := Json.mkObj [
    ("mathlib_extensions", match s.mathlibExtensions with
      | some stats => toJson stats
      | none => Json.null),
    ("definitions", toJson s.definitions),
    ("proofs", toJson s.proofs),
    ("main_theorem", toJson s.mainTheorem),
    ("proof_of_main_theorem", toJson s.proofOfMainTheorem),
    ("total_lines", toJson s.totalLines),
    ("review_burden", toJson s.reviewBurden)
  ]

/-! ## Verification Report -/

/-- Complete verification report -/
structure VerificationReport where
  /-- Project name/prefix -/
  projectName : String
  /-- Results of all checks -/
  checks : List CheckResult
  /-- Line count statistics -/
  stats : ProjectStats
  /-- Whether all checks passed -/
  allPassed : Bool
  deriving Inhabited, Repr

instance : ToJson VerificationReport where
  toJson r := Json.mkObj [
    ("project", toJson r.projectName),
    ("checks", toJson r.checks),
    ("stats", toJson r.stats),
    ("all_passed", toJson r.allPassed)
  ]

/-! ## Declaration Types -/

/-- Types of declarations we track -/
inductive DeclKind where
  | def_
  | defByProof  -- def := by ...
  | abbrev_
  | theorem_
  | lemma_
  | structure_
  | class_
  | instance_
  | axiom_
  | opaque_
  deriving DecidableEq, Repr

instance : ToString DeclKind where
  toString
    | .def_ => "def"
    | .defByProof => "def (proof)"
    | .abbrev_ => "abbrev"
    | .theorem_ => "theorem"
    | .lemma_ => "lemma"
    | .structure_ => "structure"
    | .class_ => "class"
    | .instance_ => "instance"
    | .axiom_ => "axiom"
    | .opaque_ => "opaque"

/-- A parsed declaration from source -/
structure ParsedDecl where
  kind : DeclKind
  name : String
  line : Nat
  deriving Repr

instance : Inhabited ParsedDecl where
  default := { kind := .def_, name := "", line := 0 }

/-! ## Standard Axioms -/

/-- Standard axioms that are acceptable in Lean 4 -/
def standardAxioms : List Name :=
  [ ``Classical.choice
  , ``Quot.sound
  , ``propext
  , ``funext
  -- Lean internals used by decide/native_decide tactics
  , `Lean.ofReduceBool
  , `Lean.ofReduceNat
  ]

/-- Check if an axiom is standard -/
def isStandardAxiom (ax : Name) : Bool :=
  standardAxioms.contains ax

end KMVerify
