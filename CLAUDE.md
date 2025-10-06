# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

TDCSG is a Lean 4 project for formalizing mathematics papers, built with mathlib. Currently formalizing "Two-Disk Compound Symmetry Groups" by Hearn et al., with a focus on Theorem 2.

## Project Structure

- `TDCSG.lean` - Root module that imports all library modules
- `TDCSG/TwoDisk/` - Formalization of two-disk compound symmetry groups
  - `Basic.lean` - Core definitions (TwoDiskSystem, rotations, disks)
  - `GroupAction.lean` - Group actions, orbits, finiteness
  - `PiecewiseIsometry.lean` - Piecewise isometry properties
  - `Translations.lean` - Translation sequences and polygon construction
  - `Theorem1.lean` - Characterization of infinite groups
  - `ComplexRepresentation.lean` - Complex plane and roots of unity
  - `GoldenRatio.lean` - Golden ratio properties
  - `GG5Geometry.lean` - GG₅ specific geometry at critical radius
  - `Theorem2.lean` - Main result: GG₅ is infinite at r = √(3 + φ)
- `lakefile.lean` - Lake build configuration (Lean's build system)
- `lean-toolchain` - Specifies the Lean version to use
- `two-disk_compound_symmetry_groups.tex` - Source paper being formalized

## Common Commands

### Building the Project

```bash
lake build
```

### Updating mathlib

```bash
lake update
```

### Getting mathlib cache (speeds up builds significantly)

```bash
lake exe cache get
```

### Running a single file

Open the `.lean` file in VS Code with the Lean extension installed. The file will be checked automatically.

Alternatively, use:

```bash
lake env lean TDCSG/YourFile.lean
```

### Cleaning build artifacts

```bash
lake clean
```

## Development Workflow

1. Create new formalization files in the `TDCSG/` directory
2. Import them in `TDCSG.lean` to include them in the library build
3. Use `import Mathlib` at the top of files to access mathlib theorems and tactics
4. Run `lake exe cache get` after updating dependencies to avoid long rebuild times

## Architecture Notes

- This is a standard mathlib-based Lean project
- All formalization modules should live under `TDCSG/`
- The project follows mathlib's naming and style conventions
- Use `leanprover-community/mathlib` as the dependency source for mathematical foundations

## MCP Integration

This project uses [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) for agentic interaction with Lean via the Language Server Protocol. This provides:

- Rich Lean interaction (diagnostics, goal states, term information)
- External search tools (leansearch, loogle, lean_hammer)
- Real-time feedback on proof states

The MCP server is configured in `.claude.json` and will be available when using Claude Code in this repository. Below is a list of tools offered by the repository.

## Tools

Tools are currently the only way to interact with the MCP server.

### File interactions (LSP)

#### lean_file_contents

Get the contents of a Lean file, optionally with line number annotations.

#### lean_diagnostic_messages

Get all diagnostic messages for a Lean file. This includes infos, warnings and errors.

<details>
<summary>Example output</summary>

l20c42-l20c46, severity: 1<br>
simp made no progress

l21c11-l21c45, severity: 1<br>
function expected at
  h_empty
term has type
  T ∩ compl T = ∅

...
</details>

#### lean_goal

Get the proof goal at a specific location (line or line & column) in a Lean file.

<details>
<summary>Example output (line)</summary>
Before:<br>
S : Type u_1<br>
inst✝¹ : Fintype S<br>
inst✝ : Nonempty S<br>
P : Finset (Set S)<br>
hPP : ∀ T ∈ P, ∀ U ∈ P, T ∩ U ≠ ∅<br>
hPS : ¬∃ T ∉ P, ∀ U ∈ P, T ∩ U ≠ ∅<br>
compl : Set S → Set S := fun T ↦ univ \ T<br>
hcompl : ∀ T ∈ P, compl T ∉ P<br>
all_subsets : Finset (Set S) := Finset.univ<br>
h_comp_in_P : ∀ T ∉ P, compl T ∈ P<br>
h_partition : ∀ (T : Set S), T ∈ P ∨ compl T ∈ P<br>
⊢ P.card = 2 ^ (Fintype.card S - 1)<br>
After:<br>
no goals
</details>

#### lean_term_goal

Get the term goal at a specific position (line & column) in a Lean file.

#### lean_hover_info

Retrieve hover information (documentation) for symbols, terms, and expressions in a Lean file (at a specific line & column).

<details>
<summary>Example output (hover info on a `sorry`)</summary>
The `sorry` tactic is a temporary placeholder for an incomplete tactic proof,<br>
closing the main goal using `exact sorry`.<br><br>

This is intended for stubbing-out incomplete parts of a proof while still having a syntactically correct proof skeleton.<br>
Lean will give a warning whenever a proof uses `sorry`, so you aren't likely to miss it,<br>
but you can double check if a theorem depends on `sorry` by looking for `sorryAx` in the output<br>
of the `#print axioms my_thm` command, the axiom used by the implementation of `sorry`.<br>
</details>

#### lean_declaration_file

Get the file contents where a symbol or term is declared.

#### lean_completions

Code auto-completion: Find available identifiers or import suggestions at a specific position (line & column) in a Lean file.

#### lean_run_code

Run/compile an independent Lean code snippet/file and return the result or error message.
<details>
<summary>Example output (code snippet: `#eval 5 * 7 + 3`)</summary>
l1c1-l1c6, severity: 3<br>
38
</details>

#### lean_multi_attempt

Attempt multiple lean code snippets on a line and return goal state and diagnostics for each snippet.
This tool is useful to screen different proof attempts before using the most promising one.

<details>
<summary>Example output (attempting `rw [Nat.pow_sub (Fintype.card_pos_of_nonempty S)]` and `by_contra h_neq`)</summary>
  rw [Nat.pow_sub (Fintype.card_pos_of_nonempty S)]:<br>
S : Type u_1<br>
inst✝¹ : Fintype S<br>
inst✝ : Nonempty S<br>
P : Finset (Set S)<br>
hPP : ∀ T ∈ P, ∀ U ∈ P, T ∩ U ≠ ∅<br>
hPS : ¬∃ T ∉ P, ∀ U ∈ P, T ∩ U ≠ ∅<br>
⊢ P.card = 2 ^ (Fintype.card S - 1)<br>
<br>
l14c7-l14c51, severity: 1<br>
unknown constant 'Nat.pow_sub'<br>
<br>
  by_contra h_neq:<br>
 S : Type u_1<br>
inst✝¹ : Fintype S<br>
inst✝ : Nonempty S<br>
P : Finset (Set S)<br>
hPP : ∀ T ∈ P, ∀ U ∈ P, T ∩ U ≠ ∅<br>
hPS : ¬∃ T ∉ P, ∀ U ∈ P, T ∩ U ≠ ∅<br>
h_neq : ¬P.card = 2 ^ (Fintype.card S - 1)<br>
⊢ False<br>
<br>
...
</details>

### External Search Tools

Currently all external tools are **rate limited to 3 requests per 30 seconds**. This will change based on provider feedback.

#### lean_leansearch

Search for theorems in Mathlib using [leansearch.net](https://leansearch.net) (natural language search).

[Github Repository](https://github.com/frenzymath/LeanSearch) | [Arxiv Paper](https://arxiv.org/abs/2403.13310)

- Supports natural language, mixed queries, concepts, identifiers, and Lean terms.
- Example: `bijective map from injective`, `n + 1 <= m if n < m`, `Cauchy Schwarz`, `List.sum`, `{f : A → B} (hf : Injective f) : ∃ h, Bijective h`

<details>
<summary>Example output (query by LLM: `bijective map from injective`)</summary>

```json
  {
    "module_name": "Mathlib.Logic.Function.Basic",
    "kind": "theorem",
    "name": "Function.Bijective.injective",
    "signature": " {f : α → β} (hf : Bijective f) : Injective f",
    "type": "∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Function.Bijective f → Function.Injective f",
    "value": ":= hf.1",
    "informal_name": "Bijectivity Implies Injectivity",
    "informal_description": "For any function $f \\colon \\alpha \\to \\beta$, if $f$ is bijective, then $f$ is injective."
  },
  ...
```

</details>

#### lean_loogle

Search for Lean definitions and theorems using [loogle.lean-lang.org](https://loogle.lean-lang.org/).

[Github Repository](https://github.com/nomeata/loogle)

- Supports queries by constant, lemma name, subexpression, type, or conclusion.
- Example: `Real.sin`, `"differ"`, `_ * (_ ^ _)`, `(?a -> ?b) -> List ?a -> List ?b`, `|- tsum _ = _ * tsum _`

<details>
<summary>Example output (`Real.sin`)</summary>

```json
[
  {
    "type": " (x : ℝ) : ℝ",
    "name": "Real.sin",
    "module": "Mathlib.Data.Complex.Trigonometric"
  },
  ...
]
```

</details>

#### lean_state_search

Search for applicable theorems for the current proof goal using [premise-search.com](https://premise-search.com/).

[Github Repository](https://github.com/ruc-ai4math/Premise-Retrieval) | [Arxiv Paper](https://arxiv.org/abs/2501.13959)

A self-hosted version is [available](https://github.com/ruc-ai4math/LeanStateSearch) and encouraged. You can set an environment variable `LEAN_STATE_SEARCH_URL` to point to your self-hosted instance. It defaults to `https://premise-search.com`.

Uses the first goal at a given line and column.
Returns a list of relevant theorems.
<details> <summary>Example output (line 24, column 3)</summary>

```json
[
  {
    "name": "Nat.mul_zero",
    "formal_type": "∀ (n : Nat), n * 0 = 0",
    "module": "Init.Data.Nat.Basic"
  },
  ...
]
```

</details>

#### lean_hammer_premise

Search for relevant premises based on the current proof state using the [Lean Hammer Premise Search](https://github.com/hanwenzhu/lean-premise-server).

[Github Repository](https://github.com/hanwenzhu/lean-premise-server) | [Arxiv Paper](https://arxiv.org/abs/2506.07477)

A self-hosted version is [available](https://github.com/hanwenzhu/lean-premise-server) and encouraged. You can set an environment variable `LEAN_HAMMER_URL` to point to your self-hosted instance. It defaults to `http://leanpremise.net`.

Uses the first goal at a given line and column.
Returns a list of relevant premises (theorems) that can be used to prove the goal.

Note: We use a simplified version, [LeanHammer](https://github.com/JOSHCLUNE/LeanHammer) might have better premise search results.
<details><summary>Example output (line 24, column 3)</summary>

```json
[
  "MulOpposite.unop_injective",
  "MulOpposite.op_injective",
  "WellFoundedLT.induction",
  ...
]
```

</details>

### Project-level tools

#### lean_build

Rebuild the Lean project and restart the Lean LSP server.



## License

MIT License (see [LICENSE](LICENSE))

## Best Practices for Lean 4 Formalization (Note to Future Claude)

After working on this formalization project, here are key lessons learned:

### 1. Build Management
- **Always verify builds frequently** - Lean errors can cascade, so check `lake build` after major changes
- **Watch for "No goals to be solved" errors** - These occur when you try to apply tactics after the goal is already complete. Common with `use` statements that auto-solve remaining goals
- **Remove unnecessary `rfl` and `exact` statements** - If `use x` completes the proof, don't add more tactics after it

### 2. Proof Development Strategy
- **Start with low-hanging fruit** - Prove simple lemmas first (existence statements, positivity, basic properties)
- **Use mathlib extensively** - Many properties are already proven (e.g., `goldenRatio_sq`, `phi_irrational`)
- **Decompose complex proofs** - Break into helper lemmas rather than one monolithic proof
- **Document computational proofs** - When a proof requires specific calculations (e.g., with ζ₅), add comments explaining what computation is needed

### 3. Common Patterns That Work
```lean
-- For positivity proofs
theorem foo_pos : foo > 0 := by
  unfold foo
  apply Real.sqrt_pos.mpr  -- or other positivity lemmas
  linarith  -- often solves arithmetic goals

-- For existence proofs
theorem exists_foo : ∃ x, P x := by
  use witness_value
  -- proof that P witness_value holds

-- For using existing theorems
theorem bar : Q := by
  rw [existing_theorem]  -- rewrite using known equality
  exact another_theorem  -- or apply known result
```

### 4. FreeGroup and Group Actions
- **FreeGroup is tricky** - Use `FreeGroup.lift` to map generators to group homomorphisms
- **Avoid complex recursion initially** - Start with `sorry` for `applyGroupElement` and prove properties assuming it exists
- **Document the intended implementation** - Even if using `sorry`, explain what the implementation should do

### 5. Debugging Tips
- **Use `mcp__lean-lsp__lean_goal` frequently** - Check the goal state at each line to understand what's happening
- **Read error messages carefully** - "Did not find occurrence" often means you need `simp` or to unfold definitions
- **Check for typos in tactic names** - `norm_num` not `norm_nums`, `linarith` not `linearith`
- **For multiplication order issues** - Use `mul_comm` or `rw [mul_comm a b]` to flip arguments

### 6. File Organization
- **Remove duplicate files immediately** - macOS creates "Filename 2.lean" copies that break builds
- **Keep files focused** - Each file should have a clear mathematical purpose
- **Import only what's needed** - Don't import all of Mathlib if you only need specific modules

### 7. Working with Complex Numbers
- **Norm of exponential** - `‖exp (I * θ)‖ = 1` via `Complex.norm_exp_ofReal_mul_I`
- **Rotation formulas** - Express as `center + exp(I * angle) * (point - center)`
- **Watch multiplication order** - Complex multiplication isn't always commutative with mixed types

### 8. Managing Sorries
- **Track sorry count** - Use `grep -h sorry TDCSG/TwoDisk/*.lean | wc -l` to monitor progress
- **Prioritize by dependency** - Prove foundational lemmas before high-level theorems
- **Document why sorries remain** - Add comments explaining what's blocking completion

### 9. Effective Use of Tools
- **Don't overuse search tools** - Rate limits exist (3 requests/30s), so batch searches when possible
- **Prefer local tools** - Use `Glob` and `Grep` instead of repeated `lean_loogle` calls
- **Build once, check many** - After `lake build`, use `lean_diagnostic_messages` to check multiple files

### 10. Progress Tracking
- **Use TodoWrite liberally** - Track what you've completed and what's next
- **Update README regularly** - Document progress for future sessions
- **Celebrate small wins** - Each proven lemma is progress, even simple ones

### Key Insight
The most important lesson: **Lean formalization is incremental**. You don't need to prove everything at once. Build a scaffold with `sorry`, then systematically replace them with proofs. This project went from 37 sorries to 25, and each reduction made the structure clearer and the remaining work more apparent.

Remember: The goal isn't just to eliminate sorries, but to build a clear, maintainable formalization that others (including future you) can understand and extend.
