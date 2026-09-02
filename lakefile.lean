import Lake
open Lake DSL

package «MonogateEML» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.32.2"

require MachLib from "../machlib/foundations"

@[default_target]
lean_lib «MonogateEML» where
  roots := #[`MonogateEML]
