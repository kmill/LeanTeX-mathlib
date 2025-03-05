import Lake
open Lake DSL

package "LeanTeX_Mathlib" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ]

require "leanprover-community" / "mathlib"
require "kmill" / "LeanTeX"

@[default_target]
lean_lib «LeanTeXMathlib» where
  -- add any library configuration options here
