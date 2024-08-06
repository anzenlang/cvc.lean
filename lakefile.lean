import Lake
open Lake DSL

package cvc {
  precompileModules := true
  testDriver := "cvcTest"
}

require cvc5 from
  git "https://github.com/anzenlang/lean-cvc5" @ "test_framework"

@[default_target]
lean_lib Cvc {}

lean_lib CvcTest {
  globs := #[Glob.submodules `CvcTest]
}
