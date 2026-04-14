import Lake
open Lake DSL

package «formal_anthropology» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`linter.unusedVariables, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.15.0"

@[default_target]
lean_lib «FormalAnthropology» where
  srcDir := "."
  roots := #[`FormalAnthropology]
