import Lake
open Lake DSL

package RigidityProject where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require "leanprover-community" / "mathlib" @ "git#f897ebcf72cd16f89ab4577d0c826cd14afaafc7"

@[default_target]
lean_lib RigidityProject where
  globs := #[.submodules `RigidityProject]
