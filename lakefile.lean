/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
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
  git "https://github.com/anzenlang/lean-cvc5" @ "exception_handling"

@[default_target]
lean_lib Cvc {}

lean_lib CvcTest {
  globs := #[Glob.submodules `CvcTest]
}
