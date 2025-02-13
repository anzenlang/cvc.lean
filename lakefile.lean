/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Lake
open Lake DSL

package cvc {
  precompileModules := true
  testDriver := "CvcTest"
}

require cvc5 from
  git "https://github.com/anzenlang/lean-cvc5" @ "dry_defs_macro"
require auto from
  git "https://github.com/anzenlang/lean-auto" @ "bump_4.11.0"

@[default_target]
lean_lib Cvc {}

lean_lib CvcTest {
  globs := #[Glob.submodules `CvcTest]
}
