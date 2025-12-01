# KMVerify - Kim Morrison Standard Verification Tool

A modular, project-agnostic tool for verifying Lean 4 projects comply with the Kim Morrison Standard for AI-assisted formal mathematics.

## Purpose

When AI generates formal proofs, how can humans efficiently verify they're legitimate? The Kim Morrison Standard solves this by requiring strict architectural separation:

1. **Statement file** - contains only the theorem statement
2. **Proof file** - contains only the proof
3. **Definitions directory** - isolated, human-reviewable definitions

This lets reviewers verify correctness by inspecting hundreds of lines rather than thousands.

## Usage

```bash
# Run from project root (uses km_verify.json in current directory)
lake env lean --run KMVerify/Main.lean

# Run with explicit project path
lake env lean --run KMVerify/Main.lean /path/to/project

# JSON output for CI
lake env lean --run KMVerify/Main.lean --json
```

## Configuration

Create a `km_verify.json` file in your project root:

```json
{
  "project_prefix": "MyProject",
  "source_dir": "MyProject",
  "mathlib_extensions_dir": "MathlibExtensions",
  "definitions_dir": "Definitions",
  "proofs_dir": "Proofs",
  "main_theorem_file": "MainTheorem.lean",
  "proof_of_main_theorem_file": "ProofOfMainTheorem.lean",
  "statement_name": "StatementOfTheorem",
  "theorem_name": "mainTheorem"
}
```

All paths are relative to project root. `mathlib_extensions_dir` is optional.

## Trust Tiers

### MathlibExtensions/ (Optional)
- **Imports**: Mathlib and MathlibExtensions only
- **Declarations**: Only `def := by ...` (with proof obligations), lemmas, theorems
- **Prohibited**: Plain defs, instances
- **Trust level**: Fully trusted (no project-specific definitions)

### Definitions/
- **Imports**: Mathlib, MathlibExtensions, and Definitions
- **Declarations**: All types allowed (defs, lemmas, instances, etc.)
- **Trust level**: Zero trust, requires full human review

### Proofs/
- **Imports**: Mathlib, MathlibExtensions, and Definitions
- **Declarations**: lemmas and theorems only
- **Prohibited**: defs, instances, structures, etc. anything other than theorems or lemmas
- **Trust level**: Low trust. Machine-verified, but relies on local definitions

### MainTheorem.lean
- **Imports**: Mathlib, MathlibExtensions, and Definitions (NOT Proofs)
- **Declarations**: Only defs (specifically `StatementOfTheorem : Prop`)
- **Trust level**: Zero trust, requires full human review

### ProofOfMainTheorem.lean
- **Imports**: Unrestricted
- **Declarations**: Exactly one theorem, which proves the proposition from 
- **Trust level**: Machine-verified

## Verification Checks

| Check | Description |
|-------|-------------|
| Structure | `StatementOfTheorem` and main theorem exist |
| Axioms | Only standard axioms (propext, Quot.sound, Classical.choice, funext), no sorryAx |
| Imports | Import discipline per trust tier |
| Transparency | No custom axioms or opaque declarations |
| Completeness | No sorry statements in source files |
| Proof Minimality | ProofOfMainTheorem.lean contains exactly one theorem |
| MainTheorem Purity | MainTheorem.lean contains no lemmas/theorems |
| No Instances | No instance declarations in MathlibExtensions |
| No Trivial Definitions | No `def X : Prop := True/False` patterns |
| No Duplicates | Unique definition names across files |
| Proofs Declarations | Proofs/ contains only lemmas and theorems |

## Output

```
================================================================================
KIM MORRISON STANDARD VERIFICATION
Project: TDCSG
================================================================================

TRUST TIER SUMMARY
--------------------------------------------------------------------------------
  MathlibExtensions/            [NOT PRESENT]
  Definitions/          8 files      847 lines
  Proofs/              18 files    4,231 lines
  MainTheorem.lean                    27 lines
  ProofOfMainTheorem.lean             60 lines
--------------------------------------------------------------------------------
  REVIEW BURDEN: 874 lines (Definitions + MainTheorem)
  TOTAL: 5,165 lines (17% requires review)

CHECKS
--------------------------------------------------------------------------------
  [PASS] Structure
  [PASS] Axioms
  [PASS] Imports
  [PASS] Transparency
  [PASS] Completeness
  [PASS] Proof Minimality
  [PASS] MainTheorem Purity
  [PASS] No Instances
  [PASS] No Trivial Definitions
  [PASS] No Duplicates
  [PASS] Proofs Declarations

================================================================================
RESULT: PROJECT VERIFIED
================================================================================
```

## File Structure

```
KMVerify/
  Main.lean              # CLI entry point, orchestration
  Types.lean             # CheckResult, TrustLevel, VerificationReport
  Config.lean            # Config file parsing
  FileUtils.lean         # File scanning, import extraction
  Report.lean            # Output formatting
  Checks/
    Structure.lean       # Required declarations exist
    Axioms.lean          # Only standard axioms
    Imports.lean         # Import discipline
    Transparency.lean    # No custom axioms/opaques
    Completeness.lean    # No sorry statements
    ProofMinimality.lean # Exactly one theorem in proof file
    MainTheoremPurity.lean   # No lemmas in MainTheorem
    Instances.lean       # No instances in MathlibExtensions
    TrivialDefs.lean     # Detect trivially true/false defs
    Duplicates.lean      # No duplicate definitions
    ProofsDeclarations.lean  # Only lemmas/theorems in Proofs/
  README.md
```

## Reference

Kim Morrison Standard discussion:
https://leanprover.zulipchat.com/#narrow/channel/219941-Machine-Learning-for-Theorem-Proving/topic/Discussion.3A.20AI-written.20mathematical.proofs/with/558843568

## License

Apache 2.0
