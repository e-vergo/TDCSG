import Lake
open Lake DSL

package "TDCSG" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require "leanprover-community" / "mathlib"

meta if get_config? env = some "dev" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "v4.24.0"

@[default_target]
lean_lib «TDCSG» where
  -- add any library configuration options here

lean_lib «KMVerify» where
  -- Kim Morrison Standard verification tool

lean_exe «km_verify» where
  root := `KMVerify.Main
  supportInterpreter := true

lean_exe «extract_proof_deps» where
  root := `scripts.extract_proof_deps
  supportInterpreter := true

lean_exe «extract_dep_graph» where
  root := `scripts.extract_dep_graph
  supportInterpreter := true

lean_exe «find_dead_code» where
  root := `scripts.find_dead_code
  supportInterpreter := true

lean_exe «extract_graph» where
  root := `ExtractGraph
  srcDir := "dep_graph"
  supportInterpreter := true
