/-
Copyright (c) 2025 Eric Hearn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Hearn
-/
import KMVerify.Main

/-!
# KMVerify - Kim Morrison Standard Verification Tool

A modular, project-agnostic tool for verifying Lean 4 projects comply with the
Kim Morrison Standard for AI-assisted formal mathematics.

## Usage

```bash
lake env lean --run KMVerify/Main.lean [project_root] [--json]
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

## Trust Tiers

- **MathlibExtensions/**: Imports Mathlib only, no instances, defs must have proof obligations
- **Definitions/**: Definitions and supporting lemmas
- **Proofs/**: Unrestricted
- **MainTheorem.lean**: Restricted imports, only StatementOfTheorem def
- **ProofOfMainTheorem.lean**: Unrestricted imports, exactly one theorem

## Checks

1. Structure - Required declarations exist
2. Axioms - Only standard axioms (no sorryAx)
3. Imports - Per trust tier rules
4. Transparency - No custom axioms/opaques
5. Completeness - No sorry statements
6. Proof Minimality - ProofOfMainTheorem has exactly one theorem
7. MainTheorem Purity - No lemmas in MainTheorem
8. No Instances - No instances in MathlibExtensions
9. No Trivial Definitions - No `def X : Prop := True/False`
10. No Duplicates - Unique definition names

## Reference

Kim Morrison Standard:
https://leanprover.zulipchat.com/#narrow/channel/219941-Machine-Learning-for-Theorem-Proving/topic/Discussion.3A.20AI-written.20mathematical.proofs/with/558843568
-/
