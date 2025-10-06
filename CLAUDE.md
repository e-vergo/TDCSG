# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

TDCSG is a Lean 4 project for formalizing mathematics papers, built with mathlib.

## Project Structure

- `TDCSG.lean` - Root module that imports all library modules
- `TDCSG/` - Source directory for formalization work
- `lakefile.lean` - Lake build configuration (Lean's build system)
- `lean-toolchain` - Specifies the Lean version to use

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
