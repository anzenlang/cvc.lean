High-level, strongly-typed API for the [cvc5 SMT solver][cvc5] built on top of [lean-cvc5][lcvc5].

> **NB:** cvc.lean will not build unless you run a `lake update ...` command such as `lake update
> cvc`.

- [Documentation](#documentation)
- [Depending on cvc.lean](#depending-on-cvclean)
- [Build](#build)


# Documentation

- [API documentation (WIP)](https://www.anzenlang.io/cvc.lean/doc/Cvc.html)
- [User Manual (WIP)](https://www.anzenlang.io/cvc.lean/userManual)

# Depending on cvc.lean

Cvc.lean is not on reservoir yet, you must depend on the git repository explicitly.

Toml lakefile:

```toml
[[require]]
name = "cvc"
git = "https://github.com/anzenlang/cvc.lean"
```

Lean lakefile:

```lean
require cvc from git "https://github.com/anzenlang/cvc.lean"
```



# Build

To build this library directly or as a dependency, make sure you first run `lake update cvc` to make
sure this library's main dependency, [lean-cvc5][lcvc5], builds properly.


[cvc5]: https://cvc5.github.io
[lcvc5]: https://reservoir.lean-lang.org/@abdoo8080/cvc5