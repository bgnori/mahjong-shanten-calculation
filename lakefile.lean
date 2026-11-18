import Lake

open Lake DSL

package shanten where
  srcDir := "."

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

require mahjongDomain from git "https://github.com/bgnori/mahjong-domain-core.git" @ "ed9ffbccc2707066db427ec2f855cc0bb6316133"

@[default_target]
lean_lib Shanten
