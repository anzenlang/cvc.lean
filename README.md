High-level, strongly-typed API for the [cvc5 SMT solver][cvc5] built on top of [lean-cvc5][lcvc5].

- [Documentation](#documentation)
- [Depending on cvc.lean](#depending-on-cvclean)
- [Build](#build)


# Documentation

- [API documentation (WIP)](https://www.anzenlang.io/cvc.lean/api/Cvc.html)
- [User Manual (WIP)](https://www.anzenlang.io/cvc.lean/manual/)

# Depending on cvc.lean

Cvc.lean is not on reservoir yet, you must depend on the git repository explicitly, and pin a
commit. Cvc.lean follows one Lean version at a time, the one in its `lean-toolchain`, so pick a
commit whose toolchain matches your project's. `main` only moves to a new Lean version once
[lean-cvc5][lcvc5] supports it, which can take a while after the Lean release.

Toml lakefile:

```toml
[[require]]
name = "cvc"
git = "https://github.com/anzenlang/cvc.lean"
rev = "<commit hash>"
```

Lean lakefile:

```lean
require cvc from git "https://github.com/anzenlang/cvc.lean" @ "<commit hash>"
```



# Build

`lake build` builds the library and `lake test` runs the tests. There is nothing to set up first:
[lean-cvc5][lcvc5] downloads the cvc5 release it needs as part of the build.


[cvc5]: https://cvc5.github.io
[lcvc5]: https://reservoir.lean-lang.org/@abdoo8080/cvc5
