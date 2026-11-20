import Lake

open Lake DSL

package shanten where
  srcDir := "."

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

require mahjongDomain from "../mahjong-domain-core"

@[default_target]
lean_lib Shanten
