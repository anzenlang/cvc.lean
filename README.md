A high-level, strongly-typed Lean 4 API for the [cvc5 SMT solver][cvc5], built on top of
[lean-cvc5][lcvc5].

- **Typed terms.** A term's type says its sort — `Term Int`, `Term (BitVec 8)`,
  `Term (Int → Bool)` — so an ill-sorted term does not compile, and model values come back as Lean
  values. A sort-erased API is there too, for terms whose sorts are only known at runtime.
- **The `smt!` notation** builds terms in Lean's own syntax: `smt! 0 < x ∧ x + y = 10`.
- **Solver queries checked at compile time.** Model values can only be asked for after a _sat_
  answer, unsat cores and proofs after an _unsat_ one, and terms from two different cvc5 instances
  cannot be mixed.
- **All of cvc5's theories**, plus quantifiers, synthesis, interpolation, abduction, quantifier
  elimination and proof inspection.

```lean
module
import Cvc
open Cvc Typed

public def main : IO Unit := Env.runIO do
  let solver ← Solver.new
  solver.setOpt .smt_produceModels true
  let x ← Term.mkSymbolAs Int "x"
  let y ← Term.mkSymbolAs Int "y"
  solver.assert (← smt! 0 < x ∧ x < y ∧ x + y = 10)
  solver.checkSat (ifSat := do
    println! "x = {← solver.getValue x}, y = {← solver.getValue y}")
```

prints `x = 4, y = 6`.


# Documentation

- [User manual](https://www.anzenlang.io/cvc.lean/manual/)
- [API reference](https://www.anzenlang.io/cvc.lean/api/Cvc.html)


# Using cvc.lean

cvc.lean is not on Reservoir yet: depend on its repository at a [release][releases] tag.

```toml
[[require]]
name = "cvc"
git = "https://github.com/anzenlang/cvc.lean"
rev = "vX.Y.Z"
```

or, in a `lakefile.lean`,

```lean
require cvc from git "https://github.com/anzenlang/cvc.lean" @ "vX.Y.Z"
```

then run `lake update cvc`.

- **Lean version.** Each release follows one Lean version, the one in its `lean-toolchain`, and
  your project's `lean-toolchain` must name the same. cvc.lean moves to a new Lean version once
  lean-cvc5 supports it, which can take a while after the Lean release.
- **Platforms.** Linux (x86_64 and arm64) and macOS 11 or later (Apple silicon and Intel). Windows
  is not supported yet.
- **Nothing else to install.** Each release carries a prebuilt lean-cvc5 and cvc5 for every
  platform, which the build fetches with the library: no C or C++ compiler is needed. Depending on
  a commit rather than a release tag works too, but lean-cvc5 then fetches its own files.
- **Write modules.** The typed API's guarantees rely on Lean's module system: a file using it
  should start with `module`, or its static checks do not apply.


# Building from source

`lake build` builds the library and `lake test` runs the tests and the examples. There is nothing
to set up first: lean-cvc5 downloads the cvc5 release it needs as part of the build.
`lake run buildManual` and `lake run buildApiDocs` build the documentation, and `lake run
serveManual` and `lake run serveApiDocs` serve it locally.


# License

Apache 2.0, see [LICENSE][license]. The lean-cvc5 bundles attached to releases hold cvc5's static
libraries, under cvc5's licenses and those of its dependencies, which they include.


[license]: https://github.com/anzenlang/cvc.lean/blob/main/LICENSE
[cvc5]: https://cvc5.github.io
[lcvc5]: https://github.com/abdoo8080/lean-cvc5
[releases]: https://github.com/anzenlang/cvc.lean/releases
