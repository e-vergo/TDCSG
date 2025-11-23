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
