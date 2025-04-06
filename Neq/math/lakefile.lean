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

-- Note: only used for Lean 4 v4.15.0 remove if update
@[default_target]
lean_lib «Math» {
  -- add any library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"

require smt from git "https://github.com/Lizn-zn/lean-smt" @ "v4.15.0"
