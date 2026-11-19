import Lake

open Lake DSL

package shanten where
  srcDir := "."

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

require mahjongDomain from git "https://github.com/bgnori/mahjong-domain-core.git" @ "6cbb59efcc56a45cf0f321b6cc8653d64cdadf57"

@[default_target]
lean_lib Shanten
