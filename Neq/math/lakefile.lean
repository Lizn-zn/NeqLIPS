import Lake
open Lake DSL

package «Math» {
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`relaxedAutoImplicit, true⟩,
    ⟨`linter.unusedVariables, false⟩
  ]
}

-- Note: only used for Lean 4 v4.11.0 remove if update
@[default_target]
lean_lib «Math» {
  -- add any library configuration options here
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
  ]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.11.0"

require smt from git "https://github.com/Lizn-zn/lean-smt" @ "v4.11.0"

require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.6.0"

-- require "marcusrossel" / "egg" @ git "main"
