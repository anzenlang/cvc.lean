# cvc.lean — project notes for Claude

High-level, safety-oriented Lean 4 API for the [cvc5](https://cvc5.github.io) SMT solver, built on
top of [lean-cvc5](https://github.com/abdoo8080/lean-cvc5) (`abdoo8080/cvc5`), which is a thin FFI
binding over cvc5's C++ API.

Two layers sit on that binding: **`Cvc.Untyped`**, where a term carries no Lean-side sort
information, and **`Cvc.Typed`**, where `Term α` is indexed by the Lean type its sort denotes. Term
constructors are **generated** for both layers from a single specification, so an operator is
described once rather than written twice.

## Build / test

```
lake build          # default target = lean_lib Cvc   ✅ green
lake test           # testDriver = cvcTests (globs CvcTests.* and CvcExamples.*)   ✅ green
lake run buildManual  / serveManual    # the Verso manual, see "Documentation" below
lake run buildApiDocs / serveApiDocs   # the doc-gen4 API reference
```

- Toolchain: `leanprover/lean4:v4.35.0`, and the same in `CvcManual` — keep the two in step,
  with Verso's `rev` pinned to the same version tag. The API reference's project is generated and
  follows `lean-toolchain` on its own (see "Documentation").
- One dependency: `cvc5 @ d19a134` (`inputRev = "main"`, so `lake update` moves it). lean-cvc5 tags
  every commit with its short hash and attaches its build archives to that release; `d19a134` carries
  a second tag, `0e593cc`, whose release Lake picks, with the same archives.
  `precompileModules := true` on the `cvc` package.
- **No `lake update` is needed to build.** A fresh clone builds with `lake build` alone: Lake
  clones lean-cvc5 at the manifest's revision, and lean-cvc5's `cvc5Enums` build target downloads
  the precompiled cvc5 for the platform — verified on a clean clone. lean-cvc5 has no post-update
  hook.
- **TEMPORARY, to remove: a glibc shim on Linux.** lean-cvc5's Linux cvc5 was compiled against
  glibc ≥ 2.38 and references `__isoc23_strtol`/`__isoc23_fscanf`, which the older glibc Lean links
  executables against lacks, so no executable using the library linked on Linux, the manual's
  included. [Cvc/glibc_compat.c](Cvc/glibc_compat.c) defines the two, forwarding to the classic
  functions, and the root lakefile links it into `Cvc` with `moreLinkObjs` (empty elsewhere).
  **It is compiled with Lean's own clang** (`buildLeanO`), because a plain `buildO` runs whatever
  `clang` the system `PATH` has — verified: none there, and the build fails — which runner images
  have and many users' machines do not. Lean ships the compiler's headers but no libc's, so the
  shim includes only `stdarg.h` and declares `strtol` and `__isoc99_vfscanf` itself, which also
  keeps glibc ≥ 2.38's headers from redirecting its calls to itself. It covers executables only:
  a host whose own glibc predates 2.38 presumably still fails to load lean-cvc5's precompiled
  modules, which the shim cannot reach. Entry 8 of [Cvc5Issues.md](.notes/Cvc5Issues.md) is the
  issue to file against lean-cvc5. Remove the file and its lakefile target once lean-cvc5 ships a
  cvc5 built against an older glibc.
- CI ([.github/workflows/ci.yml](.github/workflows/ci.yml)) runs on Linux, on pushes to `main` and
  PRs to `main` only, so a topic branch is **not** covered. **One job does everything in sequence**,
  on one machine, so the manual and the API reference build on the library `lake build` just built,
  in one Lake directory with nothing to hand over: `.github/scripts/check_versions.py` (the manual
  on the root's toolchain, Verso pinned to it, every package the projects sharing `.lake/packages`
  have in common at one revision), Lean, `lake build`, `lake test`, `lake run buildManual` (which
  fails on any example whose output drifts); then, on `main` only, `lake run buildApiDocs`, the
  version check again with the generated project's manifest, and the site — `api/`, `manual/`, and
  the README rendered as `index.html` (`.github/scripts/render_readme.sh`, through GitHub's Markdown
  API) — uploaded for a second `deploy` job, which publishes it with `actions/deploy-pages`. No
  branch: the repository's Pages source must be "GitHub Actions", and each deployment replaces the
  whole site.

  Separate jobs were tried and dropped: each job is a fresh machine, and a GitHub cache entry is an
  immutable snapshot that cannot be added to or merged, so parallel jobs sharing `.lake/packages`
  need one cache per part (library, Verso, doc-gen4, Lean) — a lot of machinery to save the minute
  the tests take. Running two builds concurrently inside one job would not help either: the runner
  has four cores, each build uses all of them, and both write to `.lake/packages`.

  Caches: `~/.elan`, keyed on the exact toolchain **with no fallback**, so a Lean bump starts empty
  and saves an entry holding only the new toolchain (a fallback would restore the old one and
  accumulate toolchains); and the Lake directories, saved only from `main` (the entry holds the
  library, Verso and doc-gen4) and restored everywhere, minus the API reference's build directory,
  since doc-gen4 never drops the page of a removed module. Lean is installed by
  `.github/scripts/install_lean.sh` rather than `leanprover/lean-action`, which caches no
  toolchain: it skips what the cache restored and retries the toolchain download, Lean's release
  server answering the occasional 504 (it failed the first run). A newer push cancels a superseded
  run, on `main` too. There is no `lake update` step: CI follows the committed manifest. The
  manual's `apiRoot` points at upstream's site whatever repository builds it.
- **Windows is not covered.** A trial workflow, in lean-cvc5's own Windows environment (MSYS2's
  CLANG64), built the library and passed every test but `CvcTests.Srt`, whose abstract sorts a
  lean-cvc5 bug breaks there (entry 11 of [Cvc5Issues.md](.notes/Cvc5Issues.md)). It was dropped
  rather than merged failing; the workflow and what it found are entry 1 of
  [CvcLeanIssues.md](.notes/CvcLeanIssues.md), a draft issue. The glibc shim is linked on Linux
  only, so a Windows build compiles no C of its own.
- [.github/workflows/lean-release.yml](.github/workflows/lean-release.yml) checks daily for a stable
  Lean release newer than `lean-toolchain` and opens one "Bump to Lean vX" issue per release,
  saying which version lean-cvc5 is on. Bumps are done by hand: lean-cvc5 follows Lean manually
  and with a delay, so an automated bump would nearly always fail. Dependabot
  ([.github/dependabot.yml](.github/dependabot.yml)) keeps the actions' versions current.
- [.github/workflows/release.yml](.github/workflows/release.yml) finishes a release, started by
  publishing a **pre-release** with a new `v*` tag. Not a draft: a draft's tag does not exist until
  it is published, and its files are not public, so the check could not fetch it as a user does.
  Per platform — lean-cvc5's own CI matrix minus Windows: Linux x86_64 and aarch64 on Ubuntu 22.04,
  macOS aarch64 (on `macos-15`, lean-cvc5's `macos-14` being retired) and x86_64 — a `bundle` job
  builds with lean-cvc5 **from source** (`lake build --no-cache`, in lean-cvc5's CI environment,
  libc++-15 headers on Linux) so that `ffi.o` is compiled against our Lean, then attaches
  `lean-cvc5-<Lean's target triple>.tar.gz`, packed by `lake run packLeanCvc5Bundle <dir>`. On
  macOS it sets `MACOSX_DEPLOYMENT_TARGET=11.0`, the oldest macOS cvc5's static release and Lean
  support, and checks every object of lean-cvc5's build carries it: unpinned, `ffi.o`, Lean's
  compiled modules and lean-cvc5's shared library all record the build machine's version (14 in
  lean-cvc5's own archive). A check job per platform, on a fresh machine, runs
  `.github/scripts/check_release.sh <repository URL> <tag>`, and `publish` turns the pre-release
  into a release once every check passes. No cache anywhere. On Linux the check (`check-linux`)
  runs in a bare `ubuntu:22.04` container with only `git`, `curl` and CA certificates added, and
  fails if any C compiler is present: the runner images come with compilers and headers, which
  hid the shim's need for a system `clang`. macOS has its own job (`check-macos`), since a job
  container needs a Linux runner — and what an empty `container:` value does is undocumented.

### Releases carry the lean-cvc5 build they were made with

lean-cvc5 fetches two release files of its own when built: its build archive (`preferReleaseBuild`,
fetched from `abdoo8080/lean-cvc5`'s release of the commit's tag; Lake builds from source without
it, which needs C++ standard headers Lean's sysroot does not ship) and cvc5's static release (from
`abdoo8080/cvc5`, URL hard-coded in its lakefile, no fallback — the build stops without it). Both
have disappeared before. Forking lean-cvc5 is ruled out, so instead each release attaches a bundle
per platform — cvc5's static release (minus its executable and Java bindings), lean-cvc5's
`.lake/build`, lean-cvc5's `LICENSE` — and the target `leanCvc5Bundle`, in `lean_lib Cvc`'s
`needs`, restores it into lean-cvc5's directory. Three facts make lean-cvc5 then fetch nothing,
each read in Lake's source and confirmed by an offline experiment (a fresh project, HTTP(S) sent to
a dead proxy, building only with the bundle):

- **Lake finishes a library's `needs` before processing any of its modules' imports**
  (`Module.recFetchPreSetup`, citing lean4#13598), so the restore precedes everything lean-cvc5;
- **Lake skips a dependency's build archive when its build directory exists**
  (`Package.maybeFetchBuildCache`: "do not automatically clobber prebuilt artifacts");
- **lean-cvc5's `cvc5Enums` is up to date when its trace is**, and that trace depends only on the
  URL string; it lives in the build directory, and the enum files it generates are committed.

Everything of lean-cvc5 is then *replayed*, its shared library included, at a path other than the
one it was built at. With `-v`, the replayed logs show the build machine's `curl` commands — which
is how `check_release.sh` tells a real download (naming the check's directory) from a replay.

The restore runs only when this package is a non-root git dependency, checked out at a tag, and
lean-cvc5 has no build directory. The bundle is looked up as Lake looks up release archives:
`<remote URL>/releases/download/<tag>/<bundle>`, so a fork's releases serve its own bundles. It
stages and unpacks everything before moving anything, the build directory last; any failure is a
**warning** and lean-cvc5 fetches its own files as before. Failures are caught as `BaseIO` results,
never logged as errors: an error in the log fails the build even when caught. What it cannot cover:
the lean-cvc5 repository itself (Lake still clones the pinned commit), a user on another Lean
version (traces mismatch; the fallback applies), and a user module importing `cvc5` directly before
any `Cvc` module.

Licences: cvc5's static release carries `COPYING` and `licenses/` (GMP is LGPL v3), and the bundle
keeps them; lean-cvc5's own build archives carry no licence file at all, though they hold GMP
statically linked.

## Lean 4 module system

Every file starts with `module` and uses the new import forms. Getting these wrong is the most
common build break:

- `public import M` — re-export `M` to downstream modules.
- `import all M` — needed to see `private` declarations of `M` (heavily used, since almost every
  wrapper type has `private` `toUnsafe`/`ofUnsafe` conversions).
- `public meta import Lean.Elab.Command` — for the macro/elab machinery.
- `public section` after `namespace Cvc` is the standard opener; `private def`/`public def` override
  inside it.
- [Cvc/Untyped.lean](Cvc/Untyped.lean) and [Cvc/Typed.lean](Cvc/Typed.lean) re-export their
  submodules with `public import`, and [Cvc.lean](Cvc.lean) re-exports everything, so `import Cvc`
  exposes the whole surface.
- **All of Lean is visible to users at the meta phase only.** `Basic`, `Defs`, `Ext`, `Spec/Defs`
  and `Types/Denote` must `public meta import Lean.*`, their public meta functions having Lean types
  in their signatures. So a name like `Std.TreeMap` *resolves* in a user's module and then fails in
  ordinary code with "may not access declaration … imported as `meta`". `Basic/Env.lean`, the root
  every module imports, therefore `public import`s `Std.Data.TreeMap` and `Std.Data.TreeSet`
  normally: the library uses both and users manipulate them. Anything else a user would naturally
  reach for and trips on this way belongs there too.

## Architecture

```
Cvc.lean                    → the root; public-imports everything
Cvc/Basic.lean              → the `enum_def%` macro + all enum wrappers
Cvc/Basic/Error.lean        → Cvc.Error, Res/ResT, throwUser/throwInternal/throwTodo/…
Cvc/Basic/Env.lean          → the `Ω` class, State, EnvT/Env, runUnsafe, the sort registry (‼️ core)
Cvc/Logic.lean              → SMT-LIB logic strings (QF_LIA…): structured builder + Parsec parser
Cvc/Defs.lean               → `def0%`–`def3%` + `Srt`/`Srts`/`Typ`/`ToTyp`
Cvc/Srt.lean                → sort constructors, `Typ.toSrt`, `IsArith`/`HasConcat`, `Regex`
Cvc/Types/*.lean            → the Lean types denoting SMT sorts (Set, Bag, TotalMap, Tup/Rel/Tab,
                              Record, …)
Cvc/Spec/Defs.lean          → Shape/SizeExpr/Notation/OpSpec + the `opSpecExt` extension
Cvc/Spec/Decl.lean          → the `op%` command: parses an entry and registers it
Cvc/Spec/<Theory>.lean      → the specification itself, one module per theory
Cvc/Gen.lean                → aggregates the two generators
Cvc/Gen/Term.lean           → `gen_untyped%`/`gen_typed%` + the nullable-lift generators
Cvc/Gen/SolverMode.lean     → `env_gen%`, the solver-mode monad generator
Cvc/Ext.lean                → the `smtTerm` category, `smtU!`/`smtT!`, the theory-free forms, and
                              `Cvc.Ext`, the expander (each theory declares its own forms)
Cvc/{Untyped,Typed}.lean    → layer roots
Cvc/{Untyped,Typed}/Core.lean       → `Defs`, `Value`, `Bool`, `BVar`, `View`, `Solver`, `Symbols`
                                      — what every theory needs
Cvc/{Untyped,Typed}/Core/Defs.lean  → the `Term`/`Terms` types and the layer's `smt!` alias
Cvc/{Untyped,Typed}/Core/Value.lean → `TermToValue`/`ValueToTerm` and the sort-agnostic accessors
Cvc/{Untyped,Typed}/Theory.lean     → aggregates the theories
Cvc/{Untyped,Typed}/Theory/*        → per-theory generation sites, one per theory per layer, plus
                                      `Datatype`, `Record` and hand-written `Sep` and `Quant`. A
                                      theory also declares its own `smt!` forms
Cvc/{Untyped,Typed}/Theory/Nullable/* → the lifted `<id>?` constructors, one module per theory
Cvc/{Untyped,Typed}/Core/Solver.lean → `Solver`, the sat mode monads, the driving functions
Cvc/{Untyped,Typed}/Grammar.lean    → grammar builders and `smt.grammar!`/`mkGrammar!`/`letGrammar!`
Cvc/{Untyped,Typed}/Synth.lean      → syntax-guided synthesis: `checkSynth`, its mode monads
Cvc/{Untyped,Typed}/Core/BVar.lean  → bound variables and the lambdas over them
Cvc/{Untyped,Typed}/Core/View.lean  → what views are built from: `Kids`, `TermView`/`ViewFamily`
Cvc/{Untyped,Typed}/Traverse.lean   → `Term.fold`, the zipper, `Term.walk`
Cvc/{Untyped,Typed}/View.lean       → what inspecting terms takes: `Core`, the `def.term_view`
                                      generator, and `Traverse`
Cvc/Gen/{View,TypedView}.lean       → the view generators, their registries, `def.term_view`
Cvc/Types/Denote.lean               → `Typ.Denote`, the Lean type a sort carried as data indexes
Cvc/{Untyped,Typed}/Core/Symbols.lean → the record-of-symbols API, symbols at a step
                                      (`Symbols.At k`) + `structure.symbols`
Cvc/{Untyped,Typed}/Extra/Sys.lean  → transition systems and BMC over them
Cvc/Gen/Symbols.lean        → what both layers' `structure.symbols` share
Cvc/Basic/Traverse.lean     → `FoldPre`/`FoldPost`/`WalkPre`/`WalkPost`, what a traversal does next
Cvc/Proof.lean              → layer-neutral proofs: `Proof.View`, one step taken apart, and the
                              traversal engine `foldWith`/`foldUpWith`
Cvc/{Untyped,Typed}/Proof.lean → proof inspection: the step decoder, `view`, `fold`, `foldUp`,
                              `ForIn`, `freeAssumptions`/`ruleCounts`/`trusted`
Cvc/SolverOptions.lean      → `Solver.Option`: cvc5's non-expert options as data, by category, with
                              each one's value type (`argType`) and `toStrings` for `setOption`,
                              plus a flat `abbrev` per option (`.smt_produceModels`).
                              Publicly imported by `Untyped/Core/Solver.lean`, so `Cvc` exposes it
Cvc/glibc_compat.c          → TEMPORARY: a Linux glibc shim linked into `Cvc`, see "Build / test"
CvcExamples/{Untyped,Typed}/* → worked examples, built by `lake test` as the tests are
CvcManual/                 → the Verso manual: a Lake project of its own (it requires Verso, which
                              the library must not impose), sources under `CvcManual/CvcManual/`
CvcTests/*                 → the test library (`lake test`)
```

### `Ω`, the `Env` monad and the sort registry

[Cvc/Basic/Env.lean](Cvc/Basic/Env.lean) is where to start. cvc5 has a *term manager*; terms/sorts/
solvers from different managers must never mix (runtime error). This library never exposes term
managers. Instead:

- `@[nospecialize] class Ω : Type 1 where private mk :: private scope : Type` — an instance
  witnesses "belongs to *the* term manager of the current scope". Nearly every type and function
  takes `[Ω]` implicitly.
- `structure EnvT [Ω] (m) (α)` wraps `StateRefT' IO.RealWorld State (ResT m) α`; `Env := EnvT
  BaseIO` (marked `@[expose]`).
- `EnvT.run (code : [Ω] → EnvT m α) : m (Res α)` / `Env.run` / `Env.runIO` create the state and bind
  the `Ω` instance rank-2, exactly like `ST.Ref`/`runST`. This gives the scoping property: an
  `Ω`-term cannot escape its manager's lifetime, nor meet a term of another scope.
- `private runUnsafe (code : TermManager → cvc5.EnvT m α)` and `runUnsafe'` (no manager) are the
  bridges into lean-cvc5. All wrappers go through them, via `EnvT.lift5`.

**`Ω` must not be a `Prop`, and its shape is load-bearing.** Proof irrelevance would make any two
instances of a `Prop` equal, so `@Srt ω` would *be* `@Srt ω'` and the only protection left would
be that no instance exists outside a run — which nested runs defeat both ways: an outer sort
accepted by the inner scope, and an inner scope's sort returned to the outer one, a use-after-free.
Each part of the declaration rules out a specific alternative:

- **`Type`, with a field**: a field-less (unit-like) class is merged by structure eta exactly as
  proof irrelevance merges a `Prop`;
- **the field is a type (`scope : Type`)**: the compiler erases it, so an instance is a constant
  `tagged` scalar — `def f [Ω] : Env Srt` compiles to `f (x_1 : tagged)` — with no allocation and
  no reference counting; a `Nat` field would also separate scopes but is passed as an object;
- **`@[nospecialize]`**: as data an instance is a specialization candidate, and specializing copies
  `Basic/Env.lean` bodies, private `runUnsafe`/`EnvT.lift5` included, into other modules, which
  fails with "Unknown constant `_private…runUnsafe`" at compile time.

Consequences of `Type 1`: a type *quantifying* over the scope (`[Ω] → …` inside it) is in `Type 1`
too, and such a value cannot be returned through `Env`, whose results are in `Type`. The symbol
aliases avoid that by taking the scope as a *binder* instead (`Sig.Fun [Ω] : Type`), so a `Sys` or a
constraint belongs to one scope, and code written once for every scope takes `[Ω] → …` at its own
boundary — `LinSolve.run`'s constraints. And there is no sort-erased `TermToValue Term`/`ValueToTerm
Term`: the class's field quantifies over the scope a term comes from, so an "identity" instance
would map one scope's terms to another's. `CvcTests/Scope.lean` pins the three rejections:
escaping a run, escaping into an enclosing run, and mixing two open scopes.

The scope's state is a record rather than a bare term manager, because a *declared* sort cannot be
rebuilt (see "Datatypes"):

```lean
structure State where
  private tm : Tm
  private declaredSorts : Std.HashMap String cvc5.Sort := {}
```

with `private registerSort` / `getRegisteredSort?` beside `runUnsafe`. `Srt.ofName` is the lookup,
and it fails with "no sort named `X` has been declared in this scope" rather than silently making an
incompatible twin.

### Error model

`Cvc.Error` = `internal | unsupported | user | io`, with `Error.ofUnsafe`/`toUnsafe` mapping to/from
`cvc5.Error`. `Res α := ResT Id α`, `ResT m α := ExceptT Error m α`. `EnvT` has
`MonadExceptOf Error`, and `MonadLift` instances from `BaseIO`, `IO`, `Res`, `ResT m`, `Env`.
`throwUser`/`throwInternal`/`throwTodo`/`throwUnreachable`/`throwIO` are `export`ed from `Error`.

### The sort layer

[Cvc/Defs.lean](Cvc/Defs.lean) holds the newtype machinery and the types: `Srt`, `Srts`,
`Srt.Abstract`, the pure Lean sort description `Typ` and the `ToTyp` class. The solver-indexed
types — `Proof`, `Grammar` — are declared beside `Solver` instead. [Cvc/Srt.lean](Cvc/Srt.lean)
holds the sort constructors, `Typ.toSrt`, the refinement classes with their `typs_of_*` theorems,
`Regex`, and `instance [ToTyp α] [ToTyp β] : ToTyp (α → β)` — the one that makes an arrow a function
sort.

- `Srt` — an SMT-LIB sort (`def3% Srt ← cvc5.Sort`).
- `Typ` — a *Lean-side, pure* description of a sort, mutual with `Typ?`; see below. `class ToTyp
  (α : Type)` maps Lean types to `Typ`; `Typ.of α = ToTyp.typ`, `Srt.of α = (Typ.of α).toSrt`.
- Refinements: `abbrev Typ.isArith / Typ.hasConcat : Typ → Bool` plus `theorem Typ.typs_of_isArith`
  / `typs_of_hasConcat` (`by grind`), and on top of them `class IsArith (α) [ToTyp α] : Prop` and
  `class HasConcat (α) [ToTyp α] : Prop`, whose single field is discharged by an autoparam (`by simp
  [...] <;> grind`). Instances: `IsArith Int/Rat`, `HasConcat String/(Array α)`.

#### `Typ` and `Typ?` — the first-class rule, made structural

`Typ` describes a sort; `Typ?` is `Typ` plus the sorts cvc5 calls **abstract** — the fully abstract
`?`, and `?BITVECTOR_TYPE`/`?FLOATINGPOINT_TYPE`/`?FINITE_FIELD_TYPE`/`?->`. They are mutual, and
which one a field takes is not a convention here but **cvc5's own first-class distinction**,
verified position by position:

| position | takes | because |
|---|---|---|
| `set`/`bag`/`seq` element, `arrayTo`'s *both* parameters | `Typ?` | `(Set ?)`, `(Array Int ?)`, `(Array ? Int)` are all legal |
| `function` codomain | `Typ?` | `(-> Int ?)` is legal |
| `function` domain, `nullable` element, `prod` component, `record` field | `Typ` | cvc5 rejects `(-> ? Int)`, `(Nullable ?)`, `(Tuple Int ?)`, and a non-first-class field |

So **no `Typ` denotes a sort cvc5 would reject as ill-sorted** — that is what the split buys, and
it is why there is no `Typ.abstract`: an abstract sort is not first-class, so it lives in `Typ?`,
and `Typ.prod [.abstract .bitVec, .int]`, which cvc5 refuses, does not typecheck.

Three things to know when editing:

- **An abstract container is not an abstract sort.** `mkAbstractSort SET_SORT` is literally
  `mkSetSort ?`, of sort kind `SET_SORT` — verified, not assumed. So it is `Typ.set .any`, and
  `Srt.Abstract` carries only the four kinds cvc5 really keeps abstract. There is no
  `Srt.abstract .set`: it would be exactly `Srt.set (← Srt.any)`.
- **`Typ?` mirrors `Typ`'s constructors as `@[match_pattern] abbrev`s**, so `.set .int` still
  works in terms *and* patterns. Without them dot notation resolves `.int` against `Typ?` and
  fails, since `Coe Typ Typ?` fires only for variables and named constructors.
- **`protected` breaks mutual visibility.** Inside a `mutual` block a `protected def Typ.beq`
  leaves siblings unable to resolve `Typ.beq`; the cross-references are written `Cvc.Typ.beq` for
  that reason. It is `protected` that does it, not the `?` in the name.

`Typ.toSrt` can still fail, but only on `datatype`/`uninterpreted`, whose name has to be in the
scope's registry — a fact about the scope rather than about the description.

**`Srt.toTyp` is the other direction**, with `Srt.toTyp?` beside it: the `?` form accepts the
abstract sorts, the plain one refuses them, so the signature says which positions each may occupy.
Both are `partial`, `Srt` being opaque. Two orderings in `toTyp` are load-bearing: tuples, records
and nullables are all *datatypes* to cvc5, so the narrower testers
come first; and `isInstantiated` is true even of a **non**-parametric datatype, so what actually
marks an instantiation is a non-empty `getInstantiatedParameters`. A round trip is pinned for every
case in [CvcTests/Srt.lean](CvcTests/Srt.lean).

#### Records

`Typ.record (fields : List (String × Typ))`. **Structural, not declared**: cvc5 builds the same sort
from the same fields, so `toSrt` rebuilds one rather than going through the registry — records are
`set`/`seq`/`nullable`, not `datatype`/`uninterpreted`.

**The order is part of the sort.** `{a : Int, b : Bool}` and `{b : Bool, a : Int}` are *different*
sorts, which is why the fields are a list and not a map. Underneath, cvc5 mono-morphises a record
into a datatype with one constructor and one selector per field, named after the fields and in
order — `__cvc5_record_a_Int_b_Bool` — and that is how `Srt.toTyp` reads one back.

**Distinct field names are our check, not cvc5's**, and so is **non-emptiness**. `Srt.record`
refuses two fields of one name — cvc5 accepts them and builds a datatype with two identically-named
selectors, which nothing can select unambiguously, logged in [Cvc5Issues.md](.notes/Cvc5Issues.md) —
and refuses the empty record, which cvc5 builds happily but which denotes what the empty tuple
already denotes. Both checks sit on `Srt.record` rather than on its callers, because `Typ.toSrt`
reaches cvc5 only through it and so inherits them; an autoparam could not, `toSrt` passing an array
it computes. The value spines make non-emptiness structural besides, `last`/`cons` as `Components`
does.

Two consequences of `List (String × Typ)` worth knowing before editing:

- it is a *second* nested position, so `beq`/`beq_refl`/`eq_of_beq` each gained a `…Fields`
  companion in the mutual group. The head pair must be **destructured in the pattern**
  (`(n, t) :: rest`, not `hd :: rest`), or the recursion is not structural — a projection out of an
  opaque pair is not a subterm;
- `deriving Ord` needs a `local instance [Ord α] [Ord β] : Ord (α × β)`, since core has none.
  `Ord (List ·)` exists, `Hashable (· × ·)` exists — only the product order is missing, which is
  why `Hashable` derived and `Ord` did not. The library does export one, `Cvc.instOrdProd` in
  `Types/Tuple.lean`, since a set of tuples cannot be written without it; it is at low priority,
  so another library's product order wins where both are present. Not `scoped`: a user spelling
  `Cvc.Set (Int × Bool)` without opening `Cvc` would get an unexplained missing instance.

`Srt.lean` covers **all 62 declarations of `cvc5.Sort`**, in three groups. The constructors, which
live on cvc5's `TermManager` rather than on `Sort` (`Srt.bool`/`int`/…/`tuple`/`function`, plus
`predicate`, `nullable`, `record`, `param`, `uninterpreted`, `uninterpretedConstructor`,
`unresolvedDatatype`, `finiteFieldOfString`). The 28 **testers**, generated by a local `is%` macro.
And the **accessors**, generated by a local `get%` macro that emits both forms — the plain one
fails outside its family, the `?`-suffixed one answers `none`, which is what the testers are for.

`Srt.getKind` answers a raw `cvc5.SortKind`, following `Term.getKind`, which already answers a raw
`cvc5.Kind`: wrapping a 23- or 320-variant enum to restate it is not worth it. `Defs.lean` does
`export cvc5 (Kind SortKind Op)` so that naming one costs no trip into `cvc5` — with `open Cvc`,
`Kind`, `SortKind` and `Op` all resolve.

**The export aliases the type, not its constructor namespace.** `Kind.ADD` written out fails with
`Unknown constant cvc5.Kind.ADD`, even though `cvc5.Kind.ADD` itself is fine — resolution through
the alias produces the right name but the constant lookup does not follow. Dot notation on the
expected type is unaffected and is the idiomatic spelling anyway: `.ADD`, `k == .ADD`,
`match k with | .ADD => …`, `t.getKind? = some .STORE`. An `abbrev` instead of the `export` is
worse — it makes every mention of `Kind` ambiguous against `cvc5.Kind`.

Two traps when adding to this file. `def%` leaves its arguments' types to inference, so a
constructor taking a *sort* must be written out or it silently takes a raw `cvc5.Sort` —
`Srt.nullable` and friends are spelled out for that reason. And `def%` accepts no doc comment of
its own, since it supplies `@[inherit_doc]`; a `/-- … -/` in front of one is a parse error.

### The Lean types denoting SMT sorts

[Cvc/Types/](Cvc/Types/) holds `Cvc.{Set,Bag,TotalMap,Float,FiniteField}` and the list-shaped
`Cvc.{Tup,Rel,Tab}` with their `Col`/`Cols` positions — the Lean types a sort's values inhabit, each
with its `ToTyp` instance and whatever `Ord`/`ToString`/operations it needs. They are
**layer-neutral**: a sort is the same whichever layer names it, so they sit beside the layers rather
than inside one, and [Cvc/Types.lean](Cvc/Types.lean) aggregates them.

Value *conversion* is deliberately not here — that needs a theory's constructors, so it lives in
that theory's module. These files are pure Lean.

`Shape.render` in [Cvc/Gen/Term.lean](Cvc/Gen/Term.lean) emits these names, so renaming one means
editing the generator. `Cvc.Float.RoundingMode` is *not* one of them: it is an `enum_def%` wrapper
in [Cvc/Basic.lean](Cvc/Basic.lean), shared infrastructure rather than a sort's value type.

`exp`/`sig` on `Cvc.Float` follow SMT-LIB, where `sig` counts the significand's hidden leading bit,
so the stored pattern is `exp + sig` bits — 32 for `Float 8 24`, single precision, and
`Float.ofBitVec` takes `BitVec (exp + sig)`.

### The two term layers

Both term types are rooted at lean-cvc5 and at nothing else — `def3% Term ← cvc5.Term` in
[Cvc/Untyped/Core/Defs.lean](Cvc/Untyped/Core/Defs.lean), `def3% Term α ← Cvc.Untyped.Term
(ofUntypedUnsafe / toUntypedUnsafe)` in [Cvc/Typed/Core/Defs.lean](Cvc/Typed/Core/Defs.lean). So
`Untyped.Term`, `Typed.Term α` and `cvc5.Term` are all the same type definitionally, while a plain
`import` keeps each opaque, which is what makes the layers distinct to a user. `Terms` is `Array
Term` in both, with private `ofUnsafe`/`toUnsafe` at `id`.

**Every type with a counterpart in the other layer converts under one naming scheme.** `toUntyped`
goes down and `toTyped` goes up, and two families of aliases say what the conversion does:

- **sort-indexed types** — `Term α`, `BVar α`, `NT α`, `Grammar σ`, `Solver.Heap s α β`,
  datatype `Ctor α`/`Field α β`/`Case α β`, record `Fields`, and the spines (`BVars`, `NTs`,
  datatype `Args`, tuple `Components`, `Tup.Components`, application `Args`) — answer to `erase`
  going down; going
  up, `toTypedAs` takes the index explicitly and `toTyped` infers it, aliased `typeCheckAs` and
  `typeCheck`;
- **unindexed types with both APIs** — `Solver`, the same type in both layers, and
  `Solver.Proof`, a type of its own in each over one cvc5 proof — answer to `relax` going down,
  and have a plain `toTyped`, free since there is nothing to check.

Going down is free. Going up is a **runtime sort check**, a `throwUser` on mismatch, never an
`Option`. Where the sort-erased counterpart has no type of its own — the heterogeneous lists, the
spines (a plain `Terms`), a datatype case (a plain `Term`) — only `toUntyped` exists. The `…As`
forms take the index **first**, so `t.toTypedAs Int` reads naturally under dot notation; the
up-conversions are declared in the typed modules as `_root_.Cvc.Untyped.….toTypedAs`, and the
datatype ones on the layer-neutral reflection types (`Cvc.Datatype.Ctor.toTypedAs`,
`Cvc.Datatype.Selector.toTypedAs`). An alias is an `abbrev` of the primary (`abbrev erase :=
@toUntyped`), so a proof unfolding one must name the primary too (`simp_all [BVars.erase,
BVars.toUntyped]`). `CvcTests/Conversions.lean` pins every signature. `Typed.Term.ofUntypedAs` /
`ofUntyped` remain as the non-dot spelling of going up. `FiniteField.erase` and `Float.erase` are
not conversions between layers — they drop a value-level size index — and keep their name.

**Name collisions to keep clear of:** a typed structure wrapping a sort-erased value holds it in a
private field named `untyped` (`Grammar`, `Solver.Heap`, `NT`), never `toUntyped`, which is the
public conversion. And datatype `Args`, `BVars` and `NTs` are abbreviations of `List`, so
`args.erase` resolves to `List.erase` wherever the namespaced `erase` is not in scope. The value
classes convert both ways too: `TermToValue.toUntyped`/`ValueToTerm.toUntyped` and
`Untyped.TermToValue.toTyped`/`Untyped.ValueToTerm.toTyped`, with bridging instances in both
directions (the `ValueToTerm` ones at low priority, so a direct instance wins; the bridge up checks
the term it builds).

Each `Defs.lean` also declares the layer's `scoped syntax "smt!"`, expanding to `smtU!`/`smtT!`, so
opening a layer gives the short spelling of the DSL.

**A layer's modules and its namespaces are laid out differently, on purpose.** `Cvc.Untyped.Term`
is the term type declared in `Untyped/Core/Defs.lean` *and* the namespace every generated
constructor lands in — but it is not a module: the modules are `Core/` and `Theory/`, split by what
a consumer needs rather than by what a name says. So `Cvc.Untyped.Theory.Set` is the module
while `Cvc.Untyped.Term.setUnion` is the declaration it emits. The declaration/namespace overlap on
`Term` is what the `T.<id>` delegation resolves through; the module split is free of it, module
names and declaration names living in separate tables.

Two consequences when editing. `Cvc.Untyped` and `Cvc.Typed` name *both* a module and a namespace,
so a blanket rename across the tree breaks type and namespace references — only import lines and
`gen_*% from` clauses name modules. And moving a theory between `Core/` and `Theory/` changes no
namespace, so it costs nothing but import lines.

## Generating term constructors from a single specification

**The problem it solves.** Writing every operator twice, by hand, once per layer, is what let the
typed layer fall behind the untyped one and left ~200 cvc5 operators unwrapped. One entry per term
kind is written in the *typed* form; the untyped signature is derived from it by erasure. Two
commands consume entries by name, so a theory's constructors are generated in that theory's own
module and a user compiles only the theories, and only the layer, they import.

Three files per theory: the specification, and one generation site per layer. Each generation site
imports only its own theory's specification, so a consumer never compiles specifications it does
not use. A generation site names its theory once rather than listing identifiers:

```lean
-- Cvc/Untyped/Theory/BitVec.lean
gen_untyped% from Cvc.Spec.BitVec
```

`op%` stamps each entry with the module it was declared in and a declaration index, so the
generators can select a whole theory and emit in specification order. The explicit
`gen_untyped% id, id, …` form still works for generating a subset.

Note `Cvc.Spec` (the aggregator) is *not* what `Gen.lean` or a specification module imports — they
take `Cvc.Spec.Defs` and `Cvc.Spec.Decl` directly, since the aggregator imports the theory
specifications and would otherwise cycle.

Specification syntax, in `Cvc/Spec/<Theory>.lean` — shapes reuse Lean `term` syntax and are
interpreted structurally, so no new tokens are reserved:

```lean
/-- Binary conjunction. -/
op% and (lft rgt : bool) : bool := AND infixr "∧" 35 unit true
/-- Binary addition. -/
op% add {α : IsArith} (lft rgt : α) : α := ADD infixl "+" 65 unit 0
/-- Logical negation. -/
op% not (boolTerm : bool) : bool := NOT prefix "¬" 1024 40
/-- Concatenation, whose result size is the sum of its arguments'. -/
op% bvConcat {n m : width} (lft : bitVec n) (rgt : bitVec m) : bitVec (n + m) := BITVECTOR_CONCAT
```

### Things to know before touching it

- **Generated names must be built with `mkIdent`, never written literally in a quotation.**
  Quotations resolve identifiers against `Gen.lean`'s environment, and `Gen.lean` deliberately
  imports neither layer, so a literal `Cvc.Env` is emitted unresolved and fails at the generation
  site with an `Unknown identifier …✝` error. See the `envId`/`runUnsafeId`/… constants. Note
  `envId` is `Cvc.Env`, the **monad**, not `Cvc.Basic.Env`, the module that declares it — that
  confusion produces exactly the error above.
- **An antiquotation inside `$[ … ]*` is iterated.** A constant spliced there has to be an array of
  the same length as what it accompanies (`argIds.map (fun _ => untypedTermId)`).
- **Generation-site requirements**: both layers need `import all Cvc.Basic.Env` (the bodies use the
  private `runUnsafe`) and `import all Cvc.Untyped.Core.Defs` (the term type's `ofUnsafe`/`toUnsafe`
  are private); typed sites additionally need `import all Cvc.Typed.Core.Defs` — a plain `import`
  leaves `Typed.Term α` opaque and delegation fails to typecheck — plus
  `open Cvc renaming Untyped.Term → T`.
- **Indexed operators** are declared with square brackets ahead of the binders
  (`op% bvExtract [hi lo] {n : size} (bv : bitVec n) : bitVec (hi - lo + 1) := BITVECTOR_EXTRACT`).
  Indices become *explicit* `Nat` arguments ahead of the term arguments and may appear in the
  result's sort; size variables stay implicit. The generated body goes through
  `tm.mkTermOfOp (← tm.mkOpOfIndices kind #[…]) #[…]` rather than `tm.mkTerm`. `cvc5.Op` itself
  needs no wrapper: it is created and consumed inside the generated body.
- **`SizeExpr` supports `+`, `-`, `*` and `arity`** — `hi - lo + 1` for `EXTRACT`, `n * count` for
  `REPEAT`, `n + extra` for the extensions. Subtraction is `Nat` subtraction. `arity` is the number
  of term arguments: a literal in a fixed-arity signature, the term array's `.size` in an n-ary
  one, so a result sort can depend on a runtime value. The identifier `arity` is therefore
  reserved in a size position. No entry uses it any more: `BITVECTOR_FROM_BOOLS` did, and is not
  wrapped, cvc5 forbidding terms of that kind through its API (asserting one aborts the process).
- **Constructors use a `tm` build.** `op% setEmpty {α} : set α := SET_EMPTY tm mkEmptySet` builds
  through `cvc5.TermManager.mkEmptySet` rather than `mkTerm`. The `kind` is still recorded — it is
  the kind the resulting term *has* — but is not what builds it. Three further pieces go with it:
  - **value parameters**, written `(name :! LeanType)`, are plain Lean arguments passed through
    unchanged in both layers, since there is no sort to erase (`mkBool (b :! Bool) : bool`);
  - a `tm` method receives its arguments in cvc5's order — indices, sort, values, terms — and
    **indices are converted with `.toUInt32`**, since cvc5 takes sizes as `UInt32` while
    `mkOpOfIndices` takes `Nat`;
  - `naryAs <name>` names the n-ary variant, for when `<id>N` is not the right name: the `N`
    suffix suits an operator that is the same operation at greater arity, not one whose
    distinction is singular versus plural. No entry uses it any more;
  - `tmSortOf <fn> <shape>` names the shape whose sort **cvc5's method** wants, for the methods
    that do not want the sort of the term they build. It does *not* reach the generated signature
    — see the element-sort rule below. `mkEmptySet` wants the set sort but `mkEmptySequence` wants
    the element sort, so only the latter carries the clause.
- **A constructor takes element sorts, never the sort it builds.** `setEmpty (elm : Srt)`, not
  `setEmpty (setSrt : Srt)` — polymorphic in the element exactly as Lean's own `∅ : Set α` is.
  The generated function takes one `Srt` per type variable the *arguments* leave free
  (`OpSpec.unboundRetVars`, named after the variable), and `Shape.buildSrt` in
  [Cvc/Gen/Term.lean](Cvc/Gen/Term.lean) assembles whatever cvc5's method wants out of them. A
  variable an argument already fixes is recovered with `(arg).getSort`, which is how
  `mkConstArray (ι : Srt) (default : Term)` builds the array sort from the index sort it is given
  and the element sort it reads off `default`. Typed, the index supplies those sorts, so
  `setEmpty : Env (Term (Set α))` takes nothing at all.
- **Erasure rule.** A type variable free in the *result* but bound by no argument is lost by
  erasure. Applying a kind always infers the sort from the arguments, so `op%` rejects such an
  entry — unless it is a `tm` constructor, which is exactly the case that needs it: the sort-erased
  signature takes the sort (`setEmpty (srt : Srt)`) while the typed one computes it from the index
  (`Srt.of (Set α) >>= …`). A `tm` entry with a free result variable also gets `ToTyp` binders.
- A type variable carrying refinement classes also gets a `ToTyp` binder, since `IsArith` and
  friends are stated over the variable's `Typ`.

### Two traps

- **`behavior := symbol` only protects the *leading* atom of a rule.** A secondary
  identifier-shaped atom is still reserved globally: a rule `tm <fn> sort <shape>` makes `sort` a
  keyword in every downstream module, breaking `(sort : Srt)` far from the cause. So every
  identifier-shaped atom leads its own rule — `tmSortOf`, `naryAs`.
- **`term` in a syntax rule is greedy.** `unitAs <term> <ident>` would parse the two as one
  application, which is why there is no such rule.

### Status

**253 `op%` entries**, 24 of them `tm` constructors, 28 with `smt!` notation, 27 indexed, across
thirteen theory modules per layer:

| theory | entries | coverage |
|---|---|---|
| bool | 12 | the connectives, plus the sort-generic `equal`, `distinct` and `ite` |
| arithmetic | 43 | complete: comparisons, division and modulus (total and partial), `pow`/`pow2`/`log2`/`sqrt`/`exp`, the 12 transcendentals, `toReal`/`toInt`/`isInt`, `divisible`, `iand`, `piand` |
| bit-vectors | 53 | complete but for `BITVECTOR_BIT` and `BITVECTOR_FROM_BOOLS`, which cvc5 forbids creating through its API, and the deprecated `BITVECTOR_TO_NAT` (`bvUbvToInt` replaces it) |
| arrays | 4 | `select`, `store`, `eqRange`, `mkConstArray` |
| sets | 19 | complete; comprehension is hand-written, see "Quantifiers" |
| bags | 19 | complete |
| sequences | 15 | complete |
| strings | 27 | complete |
| regex | 14 | complete |
| floating point | 39 | complete — arithmetic, predicates and every conversion |
| finite fields | 4 | complete |
| functions | 1 | `applyHo` only; `apply`/`apply2`/`apply3`/`applyN` are hand-written, see below |
| separation logic | 3 | `sepEmp`/`sepStar`/`sepWand`; `pto` and `nil` hang off a handle, see below |

Hand-written rather than generated, each for a stated reason: the tuple operators and the fifteen
relation/table kinds (no `Shape` describes a product), `APPLY_UF` application (a generated
constructor cannot inspect the term it is applying), the nullable constructors, `mkRoundingMode`
(needs the private enum conversion), `mkFiniteFieldElem` (takes its value before its sort),
`mkFloatingPointOfComponents` (duplicates `fpOfBits`), `mkBVar` (its result is a `BVar`, which no
shape can express), separation logic's `pto`/`nil` (their sorts are fixed by solver state, see
below), and the binders `FORALL`/`EXISTS`/`SET_COMPREHENSION` (a bound variable is not a shape, see
"Quantifiers").

## The `smt!` DSL

**The grammar is composed from what you import.** [Cvc/Ext.lean](Cvc/Ext.lean) declares the
`smtTerm` category, the two entry points, and only the forms that mention no theory; every other
form is declared in the theory it belongs to. Import `Cvc.Untyped.Theory.Set` and `smt!` accepts
`∪` and nothing else — no `{a := 1}`, no `match`, not even `1`, because `Theory.BitVec` and friends
pull in `Core.Defs` and `Core.Value` but not `Theory.Arith`. That is the point: a form whose theory
is absent does not parse, rather than parsing and failing later on an unknown constant.

- **In `Cvc/Ext.lean`**: `(…)`, `![lean term]`, a plain identifier, application `f a b`,
  `let x ← _; _`, and `fun (x : s) => _` (or `λ`) with the `smtQuantBinder` binders the
  quantifiers share. `fun`'s syntax is theory-free but each layer expands it in its `Core/BVar`,
  beside `Term.lambdaH`, since the sort-erased expansion needs `srtOf%` and `Ext.lean` imports no
  sort.
- **In `Theory/Arith`**: integer and real literals. In **`Core/Bool`**: `if _ then _ else _`, and
  `true`/`false`. In **`Theory/String`**: string literals. In **`Theory/Datatype`**: `match … with`.
  In **`Theory/Record`**: `{a := t}`, `{r with a := t}`, `r.a` and `e |>.a`. In **`Theory/Quant`**:
  `∀ (x y : s), _` and `∃ …`. In **`Grammar`**: `smt.grammar!`, a term of its own rather than
  an `smtTerm` form, whose alternatives are `smtTerm`s. In **`Theory/Regex`**: `regex!`, likewise a
  term of its own, over its own `smtRegex` category.
- **Generated operators** are per-theory too: an entry's
  `infixl`/`infixr`/`prefix` clause is emitted beside that theory's constructors.

`true` and `false` are the one form whose absence is not a parse error: they are *identifiers*, so
without `Core.Bool` they parse as the core identifier form and fail as `Bool` where `Term` was
wanted. Nothing can be done about that short of dropping the identifier form.

Four pieces make it work:

- **Dispatch is a `macro_rules` table, not a function.** Recursion goes through a term-level
  `smtExpand% <layer root> <smtTerm>` node, and each theory adds its own alternatives for it.
  `macro_rules` composes across modules — a later alternative is tried first and falls through to
  earlier ones on `Macro.throwUnsupported` — so a theory adds an expansion without the base module
  knowing the form exists, and a core form can contain a theory's form or the other way round. An
  environment extension would not do this: `MacroM` can resolve names but cannot read one.
- **Syntax is declared once, expansion twice.** A form's rule lives in the *untyped* module and the
  typed module (which imports it) adds only its own expansion, exactly as operator notations
  already work. Each layer's alternative declines the other's layer, so order does not matter.
- **Rule naming is the dispatch mechanism for generated operators.** Rules are named
  `smtOp.<shape>.<id>`, becoming `…Term.smtOp.binary.and` under the generation site's namespace.
  `Cvc.Ext.expandSmt` matches on the *trailing three* components, so it needs no environment lookup
  and no knowledge of where generation happened. Shapes are `binary`, `prefix`, `nary` (the bracket
  form `∧[a, b, c]`, emitted only when the operator has an n-ary function to expand to).
- **Two entry points.** `smtU!` expands to `Cvc.Untyped.Term.…` and `smtT!` to `Cvc.Typed.Term.…`,
  both fully qualified. Each layer exposes a `scoped` `smt!` alias, so `open Cvc.Typed` picks the
  typed spelling. Opening both layers makes `smt!` ambiguous.

**All of the expander's own machinery lives in `Cvc.Ext`, never in `Cvc`.** `bindArgs`, `freshId`,
`patArgs`, `occursIn`, `deferSmt`, `Layer` and the rest would otherwise sit beside the term
constructors a user opens, and a helper named like a constructor — `sub`, say — would silently
shadow `Cvc.Untyped.Term.sub` (subtraction) wherever both namespaces are open. Only the
syntax rules themselves stay in `Cvc`, their names being `smt`-prefixed and collision-free.

A real literal (`1.5`, `1.5e-3`) goes to `mkReal` **unascribed**, so Lean elaborates it against that
function's `Rat` argument through `OfScientific` — which is what keeps the DSL from having to name
`Rat` at all.

**Application is declared exactly as Lean's own `app` is**, and the precedences are the whole
trick: `trailing_parser:leadPrec:maxPrec` there becomes `syntax:lead … smtTerm:max (ppSpace colGt
smtTerm:max)+`. The gap between the rule's level and its arguments' is what makes the node flat —
at `max` the rule cannot apply to its own argument, so `f i b` parses as one node with two
arguments rather than `f` applied to `(i b)`. Declaring it at `:max` instead produces the nested
parse, which is the bug to look for if this is ever touched. It also means **the five atom rules
must sit at `:max`** (`(…)`, `![…]`, ident, num, str), wherever they are declared, since that is
where arguments are parsed;
everything else — the operators, `if`, `let`, `match` — needs parentheses in argument position,
again as in Lean.

The expansion goes through `applyN`, so it inherits flattening: `(f i) b` and `f i b` build the
same term. The two layers differ in how the arguments are spelled — an array sort-erased, an `Args`
spine typed — so `Ext.expandSmt` branches, as it already does for `match`.

Gotchas:

- **`smtTerm` must not use `behavior := symbol`** (the one exception to the convention below).
  Symbol behavior breaks the longest match between an infix token and its bracket form, so `∧[a, b]`
  fails to parse while `∧` still works.
- **Syntax category names are global.** They become `Lean.Parser.Category.<name>` with no namespace,
  so two categories of the same name anywhere in the import graph collide.
- **An antiquotation in `doElem` head position does not elaborate.** `` `(do $fn (← $a) (← $b)) ``
  is rejected; `Ext.expandSmt` builds a `>>=` chain instead (`Ext.bindArgs`), with macro-scoped
  binders.

**Where a symbol is free, borrow Lean's own spelling at Lean's own precedence**, so an expression
reads the same in both languages: `%` is `intMod` at 70, and `&&&`/`|||`/`^^^`/`<<<`/`>>>` are
`bvAnd`/`bvOr`/`bvXor`/`bvShl`/`bvLshr` at 60/55/58/75/75. `⊎` is `bagUnionDisjoint`, multiset
union having no Lean spelling to borrow. Adding a notation to an entry adds *only* the notation —
the bracket form comes from the entry's `nary` clause, which is why `⊎[…]` exists and `&&&[…]` does
not.

Notation collisions to settle before more symbols are added: `++` is taken by `seqConcat` and also
wanted by `strConcat`; `/` is wanted by both `realDiv` and `intDiv`, which is why division has no
notation at all; `<`/`≤` by arithmetic and the string comparisons; `#` by four different cardinality
and length operators. One symbol maps to one operator, so these need method-carrying-class dispatch
(`class Concat α` and friends) rather than more `op%` notations.

## Values

[Cvc/Untyped/Core/Value.lean](Cvc/Untyped/Core/Value.lean) and its typed twin hold each layer's own
`TermToValue`/`ValueToTerm`/`SrtLike`, `mkValue`/`getValue`, and the sort-agnostic introspection —
`getSort`, `getKind`, `getKids`, `getSizedKids`, `hasSymbol`/`getSymbol`. The typed classes are
*not* the sort-erased ones: a typed term is opaque to a user who imports only that layer, so a
sort-erased instance would not apply. `TermToValue.toUntyped`/`ValueToTerm.toUntyped` (both
`@[reducible]`) bridge where a delegation needs the sort-erased conversion.

**Everything tied to a sort lives in that sort's theory**, not in `Value.lean`, so importing one
theory does not compile the others. That is the instances, the readers *and* the `is…Value`
predicates: `Bool` holds `isBoolValue`/`getBoolValue`/`getBoolValue?` and `SrtLike Bool`; `Arith`
the `Int`/`Rat` readers, `getSign`, the machine-width views (`isInt32Value`/`getInt32Value` and
friends, `getReal32Value`/`getReal64Value`) and the real-algebraic accessors; `BitVec`, `String`,
`Regex`, `FiniteField` and `Float` likewise; `Seq` `getSeqValue`/`isSeqValue`, `Set`
`getSetElems`/`isSetValue`, `Array` `getConstArrayBase?`/`isConstArray`. `Value.lean` holds only
what holds whatever a term's sort. Note `Bag`'s value encoding needs integer multiplicities, so
`Untyped/Theory/Bag.lean` imports `Theory/Arith`.

Naming shortens cvc5's: `Boolean`→`Bool`, `Integer`→`Int`, `Rational`→`Rat`, `BitVector`→`BitVec`,
`Sequence`→`Seq`, `FloatingPoint`→`Float`. Two readers are renamed rather than shortened, to avoid
colliding with the `TermToValue` conversion of the same sort: `getFiniteFieldValue` is
`getFiniteFieldRepr` (it answers the raw `Int`) and `getFloatingPointValue` is
`getFloatComponents` (it answers `(exp, sig, pattern)`).

**A predicate says whether a reader will answer, not what sort a term has.** `isSetValue` is false
of a built insert spine even though the term is set-sorted, for the same reason `getSetValue` only
works on a model's answer. The typed layer narrows each predicate to the index it could be true of,
so `isInt32Value` on a `Term Rat` does not typecheck rather than answering `false`.

Three things worth knowing before touching these:

- **Do not name a `private` conversion in a body.** `Term.ofUnsafe`/`Terms.ofUnsafe` elaborate fine
  under `import all`, but a downstream `#eval` fails at *run* time with `Unknown constant
  _private.…ofUnsafe`. The types are defeq, so ascribe (`let elems : Terms ← …`) instead.
- **Delegation across layers needs a declared type and a point-free body.** `def f : A → Env (Term
  X) := T.f` typechecks where the eta-expanded `fun a => T.f a` does not — the index only unfolds
  when the whole function type is unified against the declaration's.
- **A built term is not a *value*.** `getSequenceValue`/`getSetValue` want the normal forms a model
  produces, so `mkValue` then `getValue` does not round-trip for sequences or sets — only a model
  value does. Bags and total maps are the exception: those readers walk the term's kind and
  children, so a built spine works. Asserting a `STORE_ALL` also needs cvc5's `--arrays-exp`.

`Regex` has no value conversions at all, cvc5 exposing no accessor for a regex's language: an
instance whose conversions always failed would let `getValue` at `Regex` compile and fail at run
time. `getBagValue` also refuses the
`BAG_INTER_MIN`/`BAG_DIFFERENCE_*` spines, which cvc5 never puts in a model.

## Substitution

In `{Untyped,Typed}/Core/Defs.lean`. `substitute'` takes the two parallel arrays cvc5 wants, with
their 1:1 requirement as an autoparam; `substitute` takes pairs and builds the arrays carrying the
length proof; typed `heteroSubstitute` takes pairs at differing indices. No separate `Subst` builder
was needed.

Three semantics are pinned by tests because a naive reading gets each wrong: it is **simultaneous**
(so `x↦y, y↦x` swaps rather than composing), **applied once and not to a fixed point** (a
replacement is never itself rewritten), and on a duplicated source the **earliest pair wins**. A
source may be any sub-term, not only a variable. Typed, a pair's two terms share an index — which is
what keeps the result at `α` — and getting that wrong is a type error.

## Building from a kind

Sort-erased only, in `Untyped/Core/Defs.lean`: the escape hatch below every dedicated constructor.
`Term.mkOfKind (kind) (kids)` applies a raw `Kind` and checks nothing itself — cvc5 catches most
mistakes but not all, which is why every kind otherwise has its own constructor — and cannot build
an indexed operator. `Term.replaceKids t kids` reuses `t`'s operator, through `mkTermOfOp` when it
is indexed so the indices survive, and answers a kid-less `t` as is when `kids` is empty. The walk
rebuilds through `replaceKids`. Pinned in `CvcTests/Untyped/Kind.lean`, including that an
application's first kid is the function and a quantifier's are its variable list and body.

`import Cvc.Untyped.View` / `Cvc.Typed.View` is the entry point: each re-exports its layer's `Core`,
the generator behind `def.term_view`, and `Traverse`. A **view** takes a term apart one level — its
operator as a constructor, its kids, indices and names as fields — and `def.term_view V` gathers the
views of every *imported* theory into one inductive `V`. Worked examples are
`CvcExamples/{Untyped,Typed}/Views.lean`.

**One view per theory, generated in that theory's module.** A generation site carries
`gen_untyped_view% from Cvc.Spec.X` / `gen_typed_view% from Cvc.Spec.X` beside its `gen_*%` line,
which emits `Cvc.{Untyped,Typed}.View.<Theory>` and registers it in an environment extension
(`untypedViewExt`, `typedViewExt`). `def.term_view` reads the registry, which holds exactly what the
current module imports — so importing a theory is what makes its operators visible, as for `smt!`.
What no specification describes is written by hand and registered with `register_untyped_view%` /
`register_typed_view% <View> [ctor KIND, …]`: `View.Apply` (`APPLY_UF`) in `Theory/Fun`,
`View.Quant` in `Theory/Quant`, `View.Datatype` in `Theory/Datatype`. `#untyped_views` lists the
registry with what each view skipped and why.

The aggregate has four **leaves** besides one variant `of<Theory>` per view: `value` (every
`CONST_*` kind, `CONST_ARRAY`, `UNINTERPRETED_SORT_VALUE`), `symbol` (a `CONSTANT`'s name), `bvar`
(a `VARIABLE`) and `other`, for a node no imported view takes apart. So an entry gets no view
constructor if it builds a value (a `tm` constructor taking arguments, an entry with value
parameters). Each operator also gets a `@[match_pattern] abbrev` on the aggregate, so a pattern
reads `.lt ks` rather than `.ofArith (.lt ks)`. `def.term_view` refuses, before emitting anything, a
kind owned by two views and a name used twice, naming both owners — pinned in both `View` tests.

Records, tuples and nullables are datatypes to cvc5 and are **viewed as datatypes**, by constructor
and field *name*; `Term.recordFields?`, `Term.pairComponents?` and `Term.nullableCases?` give back
their typed surface when the index is known, `none` for a non-literal.

### Sort-erased

One flat inductive per theory and a **pure** `of? : Term → Option View.X`, so the aggregate's
`V.of` is pure and the traversals run in any monad. The only failure would be an ill-formed term,
which cvc5 never builds, so it is `none`/`other` rather than an error. `Kids` (≥ 2) and `Args` (≥ 1)
are subtypes of `Terms`; `Term.indexAt?` reads an operator's indices.

### Typed

`View.X : Typ → Type`, indexed by the sort it takes apart, built in two layers so that dependent
matching never gets stuck: **parts** per result-sort head (`OnBool`, `OnInt`, `OnBitVec w`,
`OnSet γ`, `OnAny β` for a type variable…) whose constructors carry the variables the result leaves
free and *proof fields* for everything computed (`n + m = w`, a class as its `Typ` predicate), and a
**theory view** with one constructor per part at the part's sort. The abbreviations flatten that
again: `@V.lt : (α : Typ) → {h0 : α.isArith = true} → Kids α.Denote → V .bool`.

- **The viewer converts the sort-erased view**, adding sorts and proofs, and is in `Env`: reading a
  kid's sort goes through `Srt.toTyp`, which consults the registry and reads record fields through
  lean-cvc5's `BaseIO` accessors. A kid whose sort no `Typ` describes makes the typed view `none`,
  the aggregate `other`. Raising that with lean-cvc5 is pending; **no `unsafe` workaround**.
- **`Typ.Denote : Typ → Type`** ([Cvc/Types/Denote.lean](Cvc/Types/Denote.lean)) is the index a
  sort carried as data gives a term. It is computed **together with an order**
  (`denoteWithOrd : Typ → (T : Type) × Option (Ord T)`), so `.set γ` denotes `Set γ.Denote` with the
  very instance a user's own `Set` is built with; a sort with no better denotation — declared sorts,
  a container keyed on something unordered — denotes `Sorted τ`. Reducible and exposed, so `FieldOf`
  and friends see through it; its delaborator `dsimp`s, since `whnf` would unfold `Set` itself.
- **`Typed.Term.cast`** moves a term between two indices of one sort, checked by `rfl` at compile
  time. Generic code needs it: over `γ`, a set's kids are `Term (Set (ToTyp.typ γ).Denote)`, not
  `Term (Set γ)` — shown in the typed `Views` example.
- **Write handlers as `match τ, v with`, as a term, not inside `do`**: matching the sort alongside
  the view is what refines it, and only a term-level match carries the refinement to the result
  type. Sort-erased handlers are plain matches.

Traps in the generator, each found the hard way:

- **Lean promotes an index to a parameter** when every constructor leaves it uniform —
  `View.Apply`'s `τ`. The abbreviation reads its binders from the constructor's telescope, so for a
  hand-written view it keeps non-instance parameters as implicit binders; otherwise `τ` silently
  disappears.
- **An order is bound `{ord : Ord …}`, not `[Ord …]`, in an abbreviation.** A pattern cannot
  synthesize an instance; a named implicit is bound by the pattern, and a local of class type is an
  instance in the body anyway.
- **Abbreviations have `_` binder types and no result type**: with one, the holes are resolved
  before the body is seen.
- Quotation pitfalls on top of the ones under "Things to know before touching it": `$[$(e)]*` cannot
  splice an expression (bind it first); named arguments mixed with positional ones need
  `Syntax.mkApp`; a `do` whose items are all spliced elaborates as empty, so steps are nested
  functions; `let some x ← e | alt` does not parse in a `doElem` quotation; an antiquotation heading
  an application after `←`, in a `match` discriminant, or in a `do` alternative needs parentheses;
  an identifier written literally in a quotation is hygienic, so a binder the caller must see is
  built with `mkIdent`.

### Traversals

[Cvc/Untyped/Traverse.lean](Cvc/Untyped/Traverse.lean) is the engine, shared: `foldWith` takes how
a node is presented, and `ZipperOf P` carries a payload per node — `Unit` sort-erased, the node's
`Option Typ` typed. `Term.fold` takes optional `pre`/`post` (`FoldPre`: `descend | skip | stop`,
`FoldPost`: `continue | stop`); `Term.walk` the same through a zipper (`WalkPre`/`WalkPost` add
`replace` and the opt-in `replaceAndRevisit`). The typed layer adds `prePlain`/`postPlain`, called
for a node whose sort has no `Typ` — a quantifier's variable list, a constructor head — so every
node is visited by one pair or the other.

- **Monads.** Sort-erased `fold` runs in any monad, `walk` in one `Env` lifts into (rebuilding goes
  through the term manager). Typed, both need `MonadLiftT Env m`: presenting a node reads its sort.
- **Rebuilding** is `mkTermOfOp` for an indexed operator, `mkTerm` on the kind otherwise, and only
  along a path something was replaced under (dirty bits on the focus and each frame). `stop`
  rebuilds to the root, keeping every replacement.
- **Replacements keep the sort, so every ancestor stays well-sorted.** Sort-erased, and for a typed
  traversal's plain nodes, it is checked (`checkSameSort`); a typed node's replacement is a
  `Term τ.Denote`, so a wrong one does not compile.
- The typed `Zipper ρ s` is indexed by the root's type and the focus's `Option Typ`; moving answers
  a `Zipper.Any`, and matching `⟨some .int, z⟩` gives a focus of `Term Int`.



## The solver

[Cvc/Untyped/Core/Solver.lean](Cvc/Untyped/Core/Solver.lean) holds the solver type, the three mode
monads (`EnvSat`, `EnvUnsat`, `EnvUnknown`, each privately wrapping `EnvT` so a check-sat cannot be
smuggled into a block that only holds because of an earlier answer), the `Result` type, and every
function whose signature mentions no term. The typed layer is an `abbrev`, so those are inherited
rather than restated.

**A mode monad is indexed by the solver that produced the answer** — `s.EnvSatT m α`, not
`EnvSatT m α` — and that index is what rules out the second mistake these monads exist to catch.
The private lift stops a *check* being smuggled into a block that stands on an earlier answer; the
index stops a block standing on **one** solver's answer from querying **another** solver, which two
solvers in one scope otherwise make easy to write:

```
s₂.getValue x has type s₂.EnvSat Term but is expected to have type s₁.EnvSatT BaseIO ?m
```

Every modal query carries it — `getValue : s.EnvSat Term`, `unexpectedSat : s.EnvSat α` — and
`checkSat`'s branches are typed at the solver it was called on, so the two agree by construction.

Each mode monad is a `structure` with `Monad`, `MonadExcept Error`, `MonadLift m`, and a **private**
lift from `EnvT` (so user code cannot smuggle a `checkSat` into a sat-only block).
`Solver.getValue`/`getModel*`/`blockModel*` live in `EnvSat`;
`getUnsatCore`/`getUnsatCoreLemmas`/`getUnsatProof`/`getUnsatAssumptions` in `EnvUnsat`;
`getTimeoutCore*` in `EnvUnknown`. You reach them via

```lean
let x ← solver.checkSat (ifSat := do …) (ifUnsat := do …) (ifUnknown := fun e => …)
-- or checkSat? (assuming := …) whose sat/unsat branches default to `return none`
```

Defaults for the unused branches are `unexpectedSat`/`unexpectedUnsat`/`unexpectedUnknown`, which
throw a user error (optionally dumping all assertions via `dumpAssertions`).

**Every modal query has an unchecked twin in `Env`, named with a trailing `!`** — `getValue!`,
`getUnsatCore!`, `getTimeoutCore!`, `getValueSepHeap!` — defined as the modal one unwrapped through
the private `toEnv`, so the two cannot drift. It gives up both guarantees (when, and which
solver); cvc5 still refuses some wrong-state queries at run time. `Term.getValue!` takes the solver
explicitly, there being no expected mode monad to infer it from. `unexpected*` have no twin. A
second family of `!` forms, the `Option`-answering queries' failing twins (`getInterpolant!`,
`findSynth!`), is described under "null means two unrelated things in cvc5".

The lift from `EnvT` is private, but each mode monad also has a *public* `liftIO` / `MonadLift IO`,
so a branch can print or otherwise do IO directly — `println!` inside `ifSat` works, and a branch
does not have to return its values just to have the caller show them.

Supporting types: `Result := cvc5.Result` with `Result.Sat? := Bool ⊕ Unknown.Explanation`,
`Result.isSat? : Res Sat?`, `Solver.checkIsSat? : Env Result.Sat?`, `Solver.checkIsSat : Env Bool`.
`Unknown.Explanation` is one of the `enum_def%` wrappers in [Cvc/Basic.lean](Cvc/Basic.lean).

Two kinds of name still need restating on the typed side:

- anything that must be *spelled* in a signature — the mode monads and `Result` — which is why
  [Cvc/Typed/Core/Solver.lean](Cvc/Typed/Core/Solver.lean) re-exports them;
- `new`, which has no solver value to use dot notation on. Everything else resolves through the
  abbreviation: `s.setOption`, `s.push`, `s.declareSrt` work on a typed solver unchanged.

The term-touching functions are re-typed on the typed side by a local `def%` macro — the body is the
sort-erased function unchanged, since a typed term is definitionally its sort-erased one. Three
kinds resist that and are spelled out: those with a **default argument** (eta-expansion collapses
it), the `checkSat` family (it threads the mode branches), and `getValue`/`getValues` (they convert
through `TermToValue`). `Solver.getValueAs`/`getValuesAs` are the sort-erased mirror of the typed
`getValue`/`getValues`: the lift from `Env` into a mode monad is private, so converting a model term
to a Lean value has to happen inside `Untyped/Core/Solver.lean`.

`Typed/Core/Solver.lean` needs `import all` on `Cvc.Typed.Core.Defs`, so the phantom index is
transparent and the delegations typecheck, and on `Cvc.Untyped.Core.Solver`, because the lift from
`EnvT` into a mode monad is private — re-typing is the sanctioned use of it.

## Separation logic

`Cvc/{Untyped,Typed}/Theory/Sep.lean` — **the whole theory, solver functions included**. That
inverts the usual layering, a theory module importing `Solver` rather than the reverse; it works
because `Solver` imports no theory module, so each layer's `Theory.lean` can aggregate `Sep` like
any other theory.

**The heap is solver state, and that is the whole problem.** `declareSepHeap` fixes the location
and data sorts once per solver, and cvc5 checks nothing against them at construction: `(pto 1 true)`
builds happily against a `Loc × Int` heap and fails at check-sat with a type error naming
`set.union` — its heap-as-sets encoding showing through. See [Cvc5Issues.md](.notes/Cvc5Issues.md).

So `declareSepHeap` answers a **handle**, and the two heap-dependent constructors hang off it:

```lean
def Solver.declareSepHeap (s : Solver) (loc data : Srt) : Env (Solver.Heap s)   -- sort-erased
def Solver.declareSepHeap (α β : Type) [ToTyp α] [ToTyp β] : Env (s.Heap α β)   -- typed
def Heap.pto : Term α → Term β → Env (Term Bool)
def Heap.nil : Env (Term α)
```

Sort-erased the handle carries the two `Srt`s and `pto` checks its operands against them, reporting
which operand and which sort. Typed they are indices, so the mismatch does not typecheck.
`sepEmp`/`sepStar`/`sepWand` mention no heap sort and are ordinary generated constructors.

**A handle fits here, where it would not fit datatypes.** A handle's index has no `ToTyp`, so a
datatype handle could not go where a sort index is required. A heap is never a term's sort —
`sep.nil` is a term of the *location* sort, an ordinary type — so nothing asks for
`ToTyp (Heap α β)`.

Three further things the design settles:

- **The handle is indexed by its solver**, as `Proof` is, because two solvers sharing a scope may
  declare *different* heaps and cvc5 accepts that. A location of one is not a location of the
  other.
- **cvc5's "heap not declared" error becomes unreachable**: `pto` and `nil` exist only on a `Heap`,
  and only `declareSepHeap` makes one. Declaring *twice* stays a runtime check — how often a
  function has been called is not something a type here can say.
- **The typed `Heap` is a `structure`, not an abbreviation.** An abbreviation unfolds, and dot
  notation would then find the sort-erased `pto`, which would *accept* typed terms since a typed
  term is definitionally its sort-erased one. Same care `Proof` needed.

A heap's location sort is naturally *uninterpreted*, and that is an ordinary index:
`Typ.uninterpreted` carries the name and `Srt.uninterpreted` registers the sort (see
"Datatypes").

`getValueSepHeap` and `getValueSepNil` answer `Bool`-sorted **formulas** characterizing the model's
heap, not values — `(pto (as @Loc_0 Loc) 0)` and `(= (as sep.nil Loc) (as @Loc_1 Loc))` — despite
cvc5 documenting them as "the term for the heap" and "the term for nil". So both are `Term Bool`
whatever the heap's sorts, with no index to carry.

There is no `Nullable/Sep.lean`: `nullable.lift` of a separating conjunction is not something cvc5
gives a meaning to, and the operators are `Bool`-valued anyway.

## Proofs

`Solver.Proof s pc` is cvc5's proof **indexed by the solver that produced it and by the component
it was asked for** — `𝕂² cvc5.Proof`, so both indices are phantom and cost nothing. Neither is
decoration:

- the *solver*, because `proofToString` takes the producing solver and the index is what stops two
  solvers' proofs from being mixed;
- the *component*, because printing in any format but `Proof.Format.no` is legal only for a `full`
  proof, as the second trap below explains.

`Solver.Proofs s pc` is the array, `getChildren` answers it at the same `pc` — a child belongs to
the component its parent came from — and `getUnsatProof (pc := .full)` answers `EnvUnsat (s.Proofs
pc)`, so a proof is reachable only where the answer was unsat.

`getRule`, `getResult`, `getArguments` and `getChildren` are **pure**, so an unsat branch can walk a
proof without leaving the mode monad; printing is `Env`, so a branch that wants to print one has to
carry the proofs out first — the lift into a mode monad being private, as with
`getValueAs`/`getValuesAs`.

**The typed proof is a type of its own** — `def Typed.Solver.Proof := Untyped.Solver.Proof`, not
an abbreviation — so a sort-erased function refuses it and dot notation can never fall back on a
sort-erased accessor. `toUntyped`/`relax` and `toTyped` cross for free (nothing to check: a
conclusion is a formula whatever the layer). Typed, `getResult : Term Bool` and `getChildren :
s.Proofs pc`; **`getArguments` deliberately stays sort-erased** — cvc5 documents that a rule's
arguments may be of any sort, strings included, so there is no index to give them and `typeCheck` is
the way to put one on. Everything else mentions no term and is restated so that its signature names
this layer's `Proof`.

`getRewriteRule?` answers `none` unless the rule is `DSL_REWRITE` or `THEORY_REWRITE`;
`getRewriteRule` is the same thing taking that as a hypothesis, which a `match h : p.getRule`
supplies as `.inl h`/`.inr h`.

**Proofs are equal by identity**, cvc5's own `operator==` (`BEq`/`Hashable` on `Solver.Proof` in
both layers). cvc5 shares a sub-proof between the steps using it, so a proof is a DAG; it *also*
builds the same sub-proof more than once when the copies sit under different nestings of `SCOPE`s
— in the tests' congruence proof, three `ASSUME (>= x 1)` and three `EQ_RESOLVE` steps above them,
under two, three and four scopes. Its merging post-processor (`proof-pp-merge`, on by default,
taking that proof from 52 distinct steps to 41) leaves those apart, so this is how cvc5 builds
proofs rather than a bug. Identity is what cvc5 offers and what the traversals use; the copies count
separately.

### Inspection

Three modules. [Cvc/Proof.lean](Cvc/Proof.lean) is layer-neutral: **`Cvc.Proof.View P F T`**, one
constructor per decoded rule (~70: assumptions, rewriting, trusted steps, resolution, Boolean
eliminations, every `CNF_*`, equality) plus `other rule premises args`, and the traversal engine
`foldWith`/`foldUpWith`. [Cvc/Untyped/Proof.lean](Cvc/Untyped/Proof.lean) holds the decoder and the
API; [Cvc/Typed/Proof.lean](Cvc/Typed/Proof.lean) the typed API on top of it.

- **The view is parametric in what a premise, a formula and a term are.** Sort-erased it is
  `View (s.Proof pc) Term Term` (`Solver.ProofView s pc`), typed `View (s.Proof pc) (Term Bool)
  Untyped.Term`. The point of `P` is `foldUp`: the decoder `Proof.viewWith p premises` is generic in
  the premise type, so `foldUp` decodes each step *at its premises' computed values* and hands the
  user `View β F T` — `.modusPonens h imp` with `h imp : β`, which is the catamorphism a proof
  rebuild wants. No lookup from premise to value, so nothing partial.
- **Decoding is total.** A rule is decoded only when its step has cvc5's documented layout
  (premise and argument counts, polarities as Boolean constants, indices and identifiers as
  integer constants, chain-resolution polarities/pivots as `SEXPR` lists); anything else is
  `other`, holding what cvc5 gave. Arguments that only restate the conclusion (`REORDERING`'s
  clause, `THEORY_REWRITE`'s equality, `TRUST`'s formula) are dropped. Typed, each formula is
  checked Boolean (pure `getSort?`), and a step failing that is `other` too — a `Term Bool` is never
  a guess. Terms of other sorts stay sort-erased, as `getArguments` does.
- **Which rules are decoded can grow**, and a rule leaving `other` breaks a pattern `.other .R …` —
  the docstring says to match on `getRule` for undecoded rules. `View`, `View.rule`,
  `View.premises` and `View.mapM` were generated once from a table and are ordinary source now:
  adding a rule means one constructor, one line in each of those three, and a decoder case.
- **Traversals**: `fold` (pre/post with `FoldPre`/`FoldPost` — the term traversal's controls,
  moved to [Cvc/Basic/Traverse.lean](Cvc/Basic/Traverse.lean) — any monad, early exit, each
  distinct step entered once unless `revisit`), the `ForIn` instance (`for step in p`, `break`), and
  `foldUp` (bottom-up, memoized, any monad, early exit by throwing). `Solver.Proofs.fold`/`foldUp`
  do several roots at once, sharing what they visit — what non-`full` components answer. Queries:
  `size`, `ruleCounts` (an array in first-reached order, deterministic for tests), `freeAssumptions`
  (`ASSUME`s no enclosing `SCOPE` discharges, via `foldUp`), `trusted`.
- **Lemmas and unsat explanations** need no dedicated API: the `theoryLemmas` component answers one
  proof per lemma; below the `full` proof's two root scopes, `freeAssumptions` is the set of
  assertions the refutation uses; the first `chainMResolution` reached holds the clauses resolved.
- Engine traps: both loops are worklists (`repeat` over a task list), never recursion, since proofs
  can be deep; in this Lean `ForIn.forIn` has no `[Monad m]` binder, so the *instance* takes it.

Observed with cvc5 1.3.2 on the tests' problems: the `full` proof comes out with `DSL_REWRITE` and
`THEORY_REWRITE` steps even though `proof-granularity` defaults to `macro`, while the other
components keep coarse `MACRO_SR_PRED_*` steps (`other`); at `rewrite` granularity rewriting is a
single `MACRO_REWRITE`, also `other`. `ARITH_TRICHOTOMY` and `INT_TIGHT_UB` are the undecoded rules
the tests meet. **Every decoded rule but three has been seen decoded** on a real proof, pinned in
`CvcTests/ProofRules.lean`: `SAT_REFUTATION` (documented for assumption-based unsat cores, where
cvc5 produces a `TRUST` step of that very shape instead), `SPLIT` (a tautology a refutation never
needs) and `PAIRWISE_CONG` (cvc5 rewrites `distinct` away before any congruence under it) are
decoded from the documentation alone — entry 10 of [Cvc5Issues.md](.notes/Cvc5Issues.md). Producing
the eliminations takes `simplification` off, so unit assertions are not substituted away;
`FACTORING` takes `proof-chain-m-res` off; `TRUST` comes from `proof-mode pp-only`. In
`TRUST_THEORY_REWRITE` the first identifier is a *theory* id (4 for bit-vectors, 10 for sets).
`produce-unsat-cores` with `proof-mode sat-proof` makes `getUnsatProof` abort the process (entry
9); the library sets neither option, and cannot stop a user from setting both.

**Two traps, both verified:**

- **A re-typing is only reachable if it is named where dot notation looks.** `getUnsatProof` is
  re-typed rather than inherited, so what it answers is headed by this layer, and
  `Typed.Solver.Proofs` is `Array (Solver.Proof s)` rather than an alias of the sort-erased array,
  since `for`/`map`/`getElem` unfold the container and would surface a sort-erased element.
  `Terms` is `Array (Term α)` for the same reason. (The typed `Proof` being its own type now makes
  a slip here a type error rather than a silent sort-erased answer.)
- **Printing a non-`full` proof in a real format segfaults**, so the pairing is a *type*
  obligation rather than a runtime check. `toString` prints in `Proof.Format.no`, legal whatever
  the component, and asks nothing. `toStringFmt` takes the format and an autoparam'd
  `fmt = .no ∨ pc = .full`, which `grind` discharges whenever both are literals — so a correct call
  reads as though there were no obligation, and the crashing one does not compile. The component
  index exists for this. cvc5 taking the process down rather than throwing is logged as a cvc5 bug
  in [Cvc5Issues.md](.notes/Cvc5Issues.md); it is the reason a type is worth spending here at all.

## Synthesis

[Cvc/Untyped/Synth.lean](Cvc/Untyped/Synth.lean) and its typed twin. `checkSynth` asks
for a function satisfying its constraints for every input, where `checkSat` asks whether constraints
*can* be satisfied. The order is: `declareSygusVar` for the universally quantified variables,
`synthFun` for the functions to find, `addSygusConstraint`/`addSygusAssume` for the specification,
then `checkSynth` and `getSynthSolution`. `findSynth` is the other entry point, enumerating terms
rather than solving a conjecture.

`SynthResult` follows `Result`: `isSolved?` is the three-way answer (`some true` solved, `some
false` unsolvable, `none` gave up) and `isSolved` fails on the third, exactly as
`Result.isSat?`/`isSat` do.

`checkSynth` works exactly as `checkSat` does, with its own **mode monads** — `EnvSolved`,
`EnvUnsolvable`, `EnvSynthUnknown` — so `getSynthSolution` can only be called where a solution was
found. A branch the caller omits falls back on `unexpectedSolved`/`unexpectedUnsolvable`/
`unexpectedSynthUnknown`, which throw, dumping the *sygus constraints* where the sat versions dump
the assertions. `checkSynthResult`/`checkSynthNextResult` are the raw forms, and `checkSynth?`
defaults the solved and unsolvable branches to `return none` and still fails on unknown, as
`checkSat?` does.

`checkSynthNext` lives in `EnvSolved` and *also* takes the three branches, returning `EnvSolvedT m
α`: cvc5 requires it be called right after a successful check, and its own answer re-splits the
world.

These are separate types from the sat monads on purpose. `EnvUnknown` gates a *timeout core*, which
has nothing to do with a synthesis check giving up, so reusing it would let one be asked for where
it does not exist.

The `env_gen%` macro that fills a mode monad in lives in
[Cvc/Gen/SolverMode.lean](Cvc/Gen/SolverMode.lean) so that both `Solver.lean` and `Synth.lean` can
declare their own. The private lift it generates is private to the module the macro is *expanded*
in, which is what keeps each module's monads enterable only by that module's check. These monads
are indexed by their solver exactly as the sat ones are, so `getSynthSolution : s.EnvSolved Term`
cannot be reached from another solver's `checkSynth`.

The typed layer is where `Grammar σ` pays off: it already carries the parameters and the start
sort, so `synthFun symbol g : Env (Term σ)` takes nothing else and the parameters cannot disagree
with the grammar. `synthAnyFun` is the unconstrained form, folding parameters and codomain into the
index with `BVars.signatureTo` as `defineFun` does. A solution has its function's signature, so
`getSynthSolution : Term σ → Env (Term σ)` carries the index across.

Three things stay sort-erased in the typed layer, each for a reason: `findAnySynth` and
`findSynthNext` (with no grammar nothing says what sort comes back — `Untyped.Term.typeCheck` puts
an index on), and `addSygusInvConstraint`'s four arguments (a state is an arbitrary number of
variables, so the relationship between the invariant's, the transition's and the pre/post signatures
is not one an index can state).

Note lean-cvc5's `*WithGrammar`/`*WithoutGrammar` pairs are folded into `synthFun` and `findSynth`
taking `Option Grammar`, the same shape `getInterpolant`/`getAbduct` use.

## Grammars

[Cvc/Untyped/Grammar.lean](Cvc/Untyped/Grammar.lean) and its typed twin. A grammar
restricts the shape of a term the solver may produce — a `synth-fun` candidate, or an interpolant or
abduct. Its parameters and its non-terminals are both plain `mkVar` bound variables in cvc5, which
makes them trivial to swap, so **`NT` is its own type**. It converts to a term (a non-terminal
appears inside its own rules) but *not* to a `BVar`, which is the mistake worth ruling out.

`NT` is a **structure**, not a `def` alias. An alias needs `BVar`, and so `Term`, `@[expose]`d for
its identity conversions to compile across a module boundary — and exposing `Term` would make the
two layers the same type to every downstream module. A one-field structure costs nothing and stops
the cascade. The typed `NT α` wraps `Untyped.NT` rather than `BVar α`, so erasing is a projection
instead of a private-constructor call.

**A grammar belongs to the scope, not to a solver.** cvc5 builds one through a solver
(`Solver::mkGrammar`, there is no term-manager method), but any solver of the same term manager
accepts it — verified in C++ for interpolation and for `synthFun`, and pinned in both layers' tests
(a grammar from `s1` restricting `s2`'s interpolant). What cvc5 rejects is a grammar from another
*term manager*, which `Ω` already rules out. So the grammar types carry no solver index: one would
forbid something that works. (lean-cvc5's own test of the rejection uses two term managers, which is
easy to misread as two solvers.)

`Untyped.Grammar` and `Typed.Grammar σ` are structures declared in
`{Untyped,Typed}/Core/Solver.lean`, since the interpolant and abduct queries there take one. The
builders and `mkGrammar` live in `{Untyped,Typed}/Grammar.lean`, under `Grammar`, and that module
imports the solver rather than the reverse. It sits at the layer's root, not under `Theory/`: a
grammar is not a theory, and neither is synthesis, so `Synth` sits beside it. The sort-erased
structure holds the `cvc5.Grammar` itself; there is no layer-neutral grammar type.

**Both layers' grammars carry their parameters.** The sort-erased `Grammar` is a structure with a
public `boundVars`, because `synthFun` must be declared over the *very* variables the grammar was
built with, and `smt.grammar!` makes them out of sight: `s.synthFun "f" g.boundVars int g`. The
typed `Grammar σ` is indexed by the **signature it generates**: `mkGrammar` folds its parameters
with `BVars.signatureTo`, exactly as `Solver.defineFun` folds its own. With no parameters that is
the start symbol's sort, which is the shape `getInterpolant`/`getAbduct` want — both take `Option
(Grammar Bool)`. It is a `structure` wrapping the sort-erased grammar and nothing else — that one
already carries the parameters and the start sort, and holding them is what lets `synthFun` take
nothing but the grammar, so the two cannot disagree. `Grammar.toUntyped` (or `erase`) hands it over,
free; the two views share one cvc5 grammar, so a rule added through either shows in both and the
freeze applies to both.

**Going up is a runtime check, as for terms.** The sort-erased `Grammar` also records `startSrt`,
the start symbol's sort, because cvc5 offers no way to read a grammar's non-terminals back; with it,
`Grammar.signatureSrt` arrows the parameters' sorts onto the start sort (flattened, as a curried
arrow is), and `Untyped.Grammar.typeCheckAs σ` compares that with `Srt.of σ`.
`Untyped.NT.typeCheckAs α` is the same for a non-terminal, so a grammar built sort-erased can be
extended through the typed `addRule`. Both are declared in `Typed/Grammar.lean`, the typed
constructors being private there.

Both layers take the start symbol as its own argument — `mkGrammar boundVars start others` — rather
than as the head of one array. cvc5 treats the *first* non-terminal as the start symbol and then
**silently drops whatever is unreachable from it**: passing `#[cnd, start]` instead of
`#[start, cnd]` yields a grammar containing neither `start` nor its rules, with no error. Naming the
start symbol makes that unrepresentable, and makes the array's non-emptiness structural rather than
a side condition — there is no `0 < nts.size` autoparam.

What the types catch: a rule's sort must match its non-terminal's (a runtime error sort-erased, a
type error typed). What stays a runtime check: a non-terminal must belong to *this* grammar, which
is a property of a value. Every non-terminal a rule mentions has to be declared at construction.

**A grammar freezes once used.** The rule builders answer a new `Grammar`, so the API reads as
though grammars were persistent, but the object underneath is shared: after `synthFun`, cvc5 rejects
further rules. The freeze belongs to the grammar object, not to a solver — once any solver has used
it, no rule can be added through any other. Both module docstrings say so; Lean has no way to model
it. `smt.grammar!` sidesteps it by building the whole grammar in one block.

### `smt.grammar!`

```lean
smt.grammar! s (x y : Int) where
  start : Int  := x | y | if cnd then start else start
  cnd   : Bool := start ≤ start
```

A solver to build it with (any of the scope's), the parameters (quantifier-style binders), then
one line per non-terminal — the first
is the start symbol — with `|`-separated alternatives that are ordinary `smtTerm`s. `?const` and
`?var` are `addAnyConstant`/`addAnyVariable`; cvc5 prints `?var` as the parameters it inlines.

- **Syntax is declared once**, in `Untyped/Grammar.lean`, as `grammarU!`/`grammarT!` over an
  `smtGrammarBody` category; each layer adds a `scoped` `smt.grammar!` alias, as `smt!` does. The
  body is a **category, not a `syntax foo := …` abbreviation**: such an abbreviation is unresolvable
  from the rules using it ("unknown parser declaration/category/alias").
- **`?const` is `"?" ident`**, the existing `?` token followed by an identifier, so no `?const`
  token is added and `?x` keeps meaning a synthetic hole everywhere else in Lean.
- **Each rule is `withPosition(…)`**, which is what stops an alternative's application from
  swallowing the next line's non-terminal: application's arguments are `colGt`.
- **Expansion** (`Ext.expandGrammar`, shared by both layers) is a `do` block: every parameter and
  non-terminal made under a hygienic name, `mkGrammar`, then the *writer's* names bound to their
  terms — **only those some alternative mentions**, or a non-recursive start symbol would trip the
  unused-variable linter — then one `addRule`/`addAny*` per alternative.
- **The whole block is ascribed** its result type (typed: the parameters' types arrowed onto the
  start sort). Without it, binding a second grammar of another index over a `g` in the same `do`
  block left the inner block's type an unsolvable metavariable.
- **Typed, each alternative is ascribed `Env (Term sort)` under `withRef alt`**, so a mismatch is
  reported at the alternative, not as `nt_start✝` against `NT Bool` at `smt.grammar!`.
- Refused at expansion: a non-terminal declared twice, and `?` followed by anything but
  `const`/`var`.
- Beware `![` inside meta code in these modules: `rules[0]![2]` lexes as the `smt!` escape.

**Extending a grammar afterwards.** `smt.grammar!` answers the grammar alone, so two forms over the
same body also hand back what it made:

- `smt.mkGrammar!` answers `grammar × NT₁ × …` without parameters and `(grammar × P₁ × …) × NT₁ ×
  …` with some (`mkGrammarU!`/`mkGrammarT!`, `Ext.expandGrammar … (withParts := true)`). The
  parameters are **grouped with the grammar on purpose**, so that a positional destructuring
  cannot take a parameter for a non-terminal — typed that is also a type error, `BVar` against
  `NT`, but sort-erased it would not be.
- `smt.letGrammar! g ← s … where …` is a **`doElem`**, binding the grammar, parameters and
  non-terminals under the block's own names through the tuple pattern `Ext.letGrammarPattern`
  builds. The names are bound with `mkIdent id.getId` — no source position — so a non-terminal the
  rest of the block never mentions draws no unused-variable warning. Its `macro_rules` sit inside
  `namespace Untyped`/`Typed`: outside it the scoped syntax is inactive and the quotation does not
  match.

In these two forms a non-terminal may be declared **without alternatives**, `num : Int` alone —
the rule syntax's `:= alts` is optional — for rules computed from data and added afterwards;
`smt.grammar!` refuses such a line at expansion, its grammar being closed (`Ext.ruleAlts` reads a
rule's alternatives either way).

**An identifier in typed `smt!` is converted by its type, not by coercion.** The core identifier
leaf expands to `smtIdent% <layer> x`, an elaborator (`Ext.elabSmtIdent`) that elaborates `x` and,
if its type is headed by `Cvc.Typed.NT` or `Cvc.Typed.BVar`, applies that type's `toTerm` itself
(and `get` for a `Cvc.Typed.Symbols.At`, a symbol at a step).
Left to the `NT α → Term α` coercion, `(← smt! n * m)` did not elaborate: the coercion's target was
`Term ?α`, and instance resolution does not assign a metavariable outside an `outParam` — `CoeDep`
fails identically. An `outParam` conversion class would work but would put the class in every sort
error, which is ruled out. Anything that is neither type is elaborated exactly as written, so
`Term α`-against-`Term β` errors are unchanged. `Theory.Record`'s projection elaborator goes
through the same function for an identifier naming no field.

Both must be used before the freeze. A non-terminal unreachable from the start symbol is dropped
from the grammar until a rule added later reaches it, which the tests pin by printing before and
after.

## Datatypes

[Cvc/Untyped/Theory/Datatype.lean](Cvc/Untyped/Theory/Datatype.lean) holds the sort-erased half: the
declaration builders
(`Datatype.Ctor.Decl.mk`/`addSelector`/`addSelectorSelf`/`addSelectorUnresolved`,
`Datatype.Decl.mk`/`addCtor`), the reflection API (`Datatype`/`Ctor`/`Selector` accessors, with
`GetElem` and `ForIn` over constructors and selectors, and `getCtor` answering a `Res` so an index
needs no proof), the four term operators `applyCtor`/`applySelector`/`applyTester`/`applyUpdater`
with `Ctor.apply`/`Selector.apply`/`Selector.applyUpdate` beside them, and matching. The sort
constructors `Srt.datatype`/`Srt.datatypes` are in `Srt.lean` with the others;
`Solver.declareDatatype` is the short path for a datatype with no parameters and no mutual
recursion.

**A declared sort is fresh, never nominal — this is the fact the typed design turns on.** Declaring
the same datatype twice gives two *different* sorts that print identically, and cvc5 rejects any
term mixing them:

```
Subexpressions must have the same type: Type 1: Pair, Type 2: Pair
```

The same holds for `Srt.uninterpreted`, `Srt.param` and `Srt.unresolvedDatatype` — every *declared*
sort, as against every *structural* one. So `Typ` cannot rebuild one: it maps a Lean type to a `Typ`
that `Typ.toSrt` reconstructs on demand, and reconstructing does not give back the same sort.

**The registry is the answer.** `Typ` has a `datatype (name : String)` case — the *name* only — and
`Typ.toSrt` answers `Srt.ofName name`, looking the sort up in the scope's state (see "`Ω`, the `Env`
monad and the sort registry"). `Srt.datatype`, `Srt.datatypes` and `Solver.declareDatatype` register
what they create, and a second declaration under a name already taken is **rejected**. `Typ`'s
hand-written `DecidableEq`, `toString`, and `isArith`/`hasConcat`/`isFlat` all carry the case.

`Typ.uninterpreted (name : String)` is the same mechanism for the other kind of declared sort, and
for the same reason — `Srt.uninterpreted` is fresh on every call, so the name is registered and
`toSrt` looks it up. The two share one registry because SMT-LIB has one sort namespace; cvc5 does
not enforce that itself, and will happily give you a datatype and an uninterpreted sort of the same
name.

The payoff is that a datatype index is first-class. With `instance : ToTyp Pair := ⟨.datatype
"Pair"⟩` and the datatype declared, all of these work: `Set Pair`, `Array Pair`, `Int → Pair`,
`Int × Pair`, `Solver.declareConstAs Pair`.

[Cvc/Typed/Theory/Datatype.lean](Cvc/Typed/Theory/Datatype.lean) finishes it. Everything there takes
the **index**, never a handle, because the sort is in the registry:

```lean
let mkC ← Datatype.ctor Pair "mk"          -- Ctor Pair
let fst ← mkC.field Int "fst"              -- Field Pair Int
let p   ← mkC.apply2 seven tru             -- Term Pair
let f   ← fst.get p                        -- Term Int
let b   ← mkC.is p                         -- Term Bool
```

Which constructors a datatype has, and what sort each field is, are runtime facts about the
declaration rather than static ones. So `Datatype.ctor` and `Ctor.field` look their names up and
**check**, then the `Ctor α` / `Field α β` carries the index from there — the
`Untyped.Term.typeCheck` trick, applied once where a name becomes a Lean type. `Ctor.apply` checks
arity and argument sorts itself rather than leaving them to cvc5, so the message names the
constructor and the offending position.

Three things to know:

- **`Field`, not `Selector`.** `Datatype.Selector` is the sort-erased reflection type, and a typed
  one of the same name is picked up ahead of it wherever both are open.
- **`Args` carries a `ToTyp` field** it does not otherwise need — `List ((β : Type) × ToTyp β ×
  Term β)`, shaped exactly like `BVars`. Without it the sigma's layout is unknown across a module
  boundary and `Args.erase` fails to compile.
- **`Args.erase` folds left**, where `BVars.erase` folds right: `Args.cons` reads in field order,
  `BVars.push` prepends. Getting this wrong silently reverses a constructor's arguments — the sort
  check caught it.

### Matching

**`MATCH` needs bound variables, not binders**, which is why it is not a quantifier-style item. A
case binds its constructor's fields to plain `mkBVar` variables and everything is an ordinary
`mkTerm`, so `Untyped/Theory/Datatype.lean` carries it as three hand-written functions:

| kind | arity | children |
|---|---|---|
| `VARIABLE_LIST` | n > 0 | the bound variables |
| `MATCH_CASE` | 2 | an `APPLY_CONSTRUCTOR` pattern, the body — nullary constructors only |
| `MATCH_BIND_CASE` | 3 | `VARIABLE_LIST`, the pattern, the body |
| `MATCH` | n > 1 | the scrutinee, then the cases |

`Term.matchBindCase` takes the `BVars` and builds the variable list itself, so `VARIABLE_LIST` never
has to be spelled. A **catch-all** is a bind case whose pattern is the bound variable alone, which
is how a match covers the constructors it does not name.

Two conditions are cvc5's to check, both being properties of the declaration rather than of any
term: coverage (`cases for match term are not exhaustive`) and agreement between the bodies
(`incomparable types in match case list`). Both come back tagged `[internal]`.

The typed side adds `Datatype.Case α β` — one case of a match on a `Term α` whose bodies are
`Term β`. The index makes the second of those two runtime errors a type error. What stays a runtime
check is what `Ctor.apply` already checks: `Ctor.case` verifies the bound variables against
`Ctor.fieldSorts`, with `case0` through `case3` for the fixed arities and `Datatype.caseAny` for the
catch-all. `Term.mkMatch` takes an `Array (Case α β)` with a `0 < size` autoparam.

There is **no HOAS variant to design here**. A constructor's field count and sorts are runtime
facts, so a Lean function of the fields cannot be typed; `BVars` is the honest surface, exactly as
with `Solver.defineFun`, and cases collect right to left through `BVars.push` the same way.

### `smt! match … with`

The DSL spells a match the way Lean does, and binds the fields itself:

```lean
smt! match l with
  | cons h t => h * 2 + 1
  | nil      => 0
```

`smtMatch` is a fixed form, not an `op%` entry, so it is hand-expanded rather than generated. It is
declared and expanded in `Cvc/{Untyped,Typed}/Theory/Datatype.lean` — a theory's forms belong to
that theory, so `smt!` accepts `match` only where datatypes were imported. The two layers build a
case differently enough to be separate functions, `Ext.expandMatchAltU` and `Ext.expandMatchAltT`.

Shared decisions:

- **The catch-all is `_` and nothing else.** A bare identifier is always a constructor name.
  cvc5 reads a lone *variable* pattern as the catch-all, and a nullary constructor pattern is the
  same syntax, so the two have to be told apart by spelling. Nothing is lost: a catch-all body can
  name the scrutinee directly.
- **`Layer` has a `root`**, since the expansion reaches `BVar.mk`, which is not in `Term`. `ops` is
  derived (`root ++ Term`).
- **`$x.field` in a quotation parses as `$(x.field)`** and fails on `TSyntax`. Write `($x).field`.
- **Pattern variables are spliced as the writer wrote them**, never through `mkIdent`, or hygiene
  would hide them from the body; everything the expansion binds for itself is macro-scoped.
- **A macro's names resolve at the use site**, and a form's *grammar* comes from its theory too, so
  a file writing `smt! match` must import that layer's `Datatype` module — without it the syntax
  does not parse at all. `Ext.lean` imports neither layer.
- Cases are tried in order and cvc5 accepts a catch-all anywhere, so a leading one shadows what
  follows — the same reading Lean's `match` has, and nothing to enforce.

**Sort-erased.** Three helpers in `Untyped/Theory/Datatype.lean` carry what the expansion knows (a
constructor's *name* and how many variables were written after it) into what cvc5 needs:
`Term.ctorOf`, `Constructor.checkArity` and `Constructor.mkBVarAt`, the last taking the field's
declared sort off the selector. A variable is bound twice — to the `BVar` the case needs, and under
the writer's name to `.toTerm`, so no coercion fires in the body. A **sort ascription** is rejected
here, a field's sort coming from the declaration.

**Typed.** The design turns on one fact: *a field the body ignores has no index to infer one from*.
Requiring an ascription for those would be unusable — `| cons h t => h` is the common shape, and
the tail is nearly always unused. So instead **every field is bound
sort-erased** via `Ctor.mkBVarAt`, and only the fields the body mentions are re-typed with
`Untyped.Term.typeCheck`. `Ctor.caseErased` is the entry point that takes `Untyped.BVars`; `case` is
defined on top of it. Sort safety is unaffected: an unused variable was built at the declared sort
and never re-typed, and a used one is checked.

- A re-typed variable is bound **under the writer's name**, so a mismatch in the body names the
  variable rather than a macro-scoped `smtTyped0✝`.
- One that is only *ascribed*, never used, is bound out of sight instead — its check is the whole
  point, and binding it visibly tripped the unused-variable linter.
- **`occursIn` respects shadowing.** A nested alternative or `let` rebinding the name is talking
  about a different variable. Getting this wrong made the outer `h` of a nested match look used, and
  it went stuck on `ToTyp ?m`. The binder identifiers of a shadowing pattern must not count as
  occurrences either — only its ascription types can still name the outer variable.

Where an ascription is still needed, and why each is not a bug:

- a **nested match's scrutinee** (`| cons h (t : Lst) => match t with …`) — the only thing that
  mentions `t` is the match that wants its index, so there is nowhere else for it to come from;
- a body whose index reaches it only through an **enclosing** match's expected type — inference
  crosses one level (`example : Env (Term Int) := smt! match l with | cons h t => h | _ => 0`
  works) but not two;
- a used variable in a position that does not pin its index down, such as `equal h h`.

## Quantifiers

`Cvc/{Untyped,Typed}/Theory/Quant.lean`, plus `setComprehension` in each layer's `Theory/Set`.
**Hand-written, not an `op%` mode**: a bound variable is not something `Shape` describes, and these
kinds would get neither a notation nor a nullable lift from the generator. `LAMBDA` and `MATCH`
were already hand-written for the same reason, and a quantifier is the `LAMBDA` construction with
another kind.

Two spellings per layer:

- **`mkForall`/`mkExists`** over a `BVars`, as `BVars.lambda`. Non-emptiness is an autoparam
  (`0 < bvs.size` sort-erased, `bvs ≠ []` typed): cvc5 rejects an empty variable list.
- **`forallH`/`existsH`**, the body a Lean function of the variables, through a `Binder φ` class
  with one instance for `Term α → Env (Term Bool)` and one for `Term α → ψ`. There is **no
  instance for a bare body**, so binding nothing does not typecheck, and none at a non-`Bool`
  codomain. Sort-erased, `Binder` and `Binder.bindAll` live in `Core/BVar`, shared with
  `Term.lambdaH`; typed, the lambda has its own `LambdaBinder`, the quantifier's being fixed at
  `Bool`. Typed, a variable's sort comes from its argument's type, so `fun (x : Term Int) => …`
  needs the annotation when the body does not pin it; names are optional (`x0`, `x1`, … by
  position). Sort-erased, the sorts are given beside the names as `List (String × Srt)`, and
  `Binder.arity` lets `bindAll` compare that list's length with the function's arity **before**
  making any variable — checking only at the last binder reported the wrong count.

`smt! ∀ (x y : s) (b : t), body` / `∃` expand to `forallH`/`existsH`, binding each variable under
the writer's own identifier (so the body sees it, and cvc5 prints that name). What follows the colon
is a Lean type typed, the variable's index, and **a Lean type or a `Srt`** sort-erased — see "A sort
written either way". The body extends right as Lean's does, so a quantifier in argument position is
parenthesized.

Each pinned by a test or documented in the code:

- **`WITNESS` is not wrapped**: asserting a term containing one *aborts the process* (`WITNESS
  should never appear in asserted terms`), logged in [Cvc5Issues.md](.notes/Cvc5Issues.md).
- **`SET_COMPREHENSION` needs all three children** (variables, predicate, element) and solving over
  one needs `sets-exp`; even then cvc5 answers `unknown` on a simple membership. Typed, the index is
  the element term's, the bound variables' sorts never reaching it.
- `forall` and `exists` are Lean keywords and cannot name a declaration, hence `mkForall`.

What is left is instantiation patterns: an optional third child, which would be an optional
argument to `mkForall`/`mkExists`, sort-erased in both layers since a pattern mixes sorts.

### `regex!`

`Cvc/{Untyped,Typed}/Theory/Regex.lean`. Regexes in the usual notation, over an `smtRegex` category
of their own rather than as `smtTerm` forms — a regex is not a formula, and the operators (`*`, `|`,
juxtaposition) would collide with `smt!`'s. Syntax and the shared `Ext.expandRegex` live in the
untyped module; each layer adds a `scoped` `regex!` → `regexU!`/`regexT!`, as for `smt.grammar!`.

| form | expands to |
|---|---|
| `"abc"`, `'a'` | `strToRegex (mkString …)` — Lean's literals, so Lean's escapes, and `"."` is a dot |
| `x`, `![e]` | a regex term in scope, any Lean term — both ascribed the layer's regex type |
| `.`, `∅` | `reAllChar`, `reNone` (`.*` is every string, so `re.all` needs no token) |
| `['a'-'z' '_']`, `[^ …]` | a union of `reRange`s and characters; `reDiff reAllChar` of that |
| `r*` `r+` `r?` `r{n}` `r{n,m}` | `reStar`, `rePlus`, `reOpt`, `reRepeat n`, `reLoop n m` |
| `¬ r`, `r s`, `r ∩ s`, `r ∖ s`, `r \| s` | complement, concatenation, intersection, difference, union |

Precedence is the usual one: postfix and `¬` at `max`, juxtaposition at `lead` (the `smtApp` trick,
so `a b c` is one flat node), `∩`/`∖` at 20, `|` at 10. **No token is added**: every symbol already
exists in Lean (`¬` rather than `~`, `∩` rather than `&`, `∅` rather than `⊤`).

Things to know:

- **The regex theory publicly imports the string theory**: a literal is a string term lifted
  with `str.to_re`. No cycle — the string module does not import the regex one.
- **`noWs` produces no node**, so in `r{n}` the count is `stx[2]`, not `stx[3]` — the off-by-one
  surfaced as "elaboration function for `«}»` has not been implemented".
- **A term the writer supplies is ascribed under `withRef`** (`Term Regex` typed, `Term`
  sort-erased), so `regex! s*` with `s : Term String` reports `s` rather than a `smtRe0✝` binder.
- cvc5 prints a shared sub-regex with `let`, so `digit+ ("." digit+)?` prints `_let_1` twice.

### A sort written either way

Wherever the DSL lets a sort be written — a quantifier's or a grammar's binders, a grammar's
non-terminals, a record field's stated sort — the sort-erased layer accepts **a Lean type or a
`Srt`**, mixed freely: `(x : Int) (y : int)`. Typed, binders and non-terminals take only a Lean
type, it being the index; a record's stated sort, being a check, takes either.

`int` and `Int` are both identifiers, so which was written is only known once the term is
elaborated, which a macro cannot do. `srtOf% e` in [Cvc/Srt.lean](Cvc/Srt.lean) is a **term
elaborator**: it elaborates `e`, answers `Srt.of e` if its type is a sort and `pure e` if it is
`Srt`, and otherwise reports ``expected a Lean type or a `Srt`, but `n` has type Nat``. Its answer
is an `Env Srt` either way, so expansions *bind* it (through `bindArgs`, or `← ` in `smt.grammar!`'s
`do` block) rather than splice it. Expansions parenthesize what they pass, so the message unwraps a
`paren` node to show what the writer wrote.

## Records

`Cvc/Types/Record.lean`, `Cvc/{Untyped,Typed}/Theory/Record.lean`. A record is a **datatype
underneath and structural on top**, and both halves matter: cvc5 mono-morphises
`{a : Int, b : Bool}` into a datatype named `__cvc5_record_a_Int_b_Bool`, one constructor and one
selector per field,
but builds the *same* sort from the same fields — unlike every declared datatype, where a second
declaration is a fresh sort. That is why `Typ.record` rebuilds a record sort rather than looking one
up in the scope's registry.

**A record must have at least one field.** cvc5 builds the empty record sort happily, but it denotes
what the empty tuple already denotes, so `Srt.record` refuses it — and because `Typ.toSrt` reaches
cvc5 only through that function, every path inherits the refusal. Field names must also be distinct,
which is our check and not cvc5's. Both live on `Srt.record` for the same reason.

**The order of the fields is part of the sort.** `{a : Int, b : Bool}` and `{b : Bool, a : Int}` are
different sorts whose terms cvc5 refuses to mix. Everything below is shaped by that: the index is a
list, and the DSL borrows Lean's structure-instance syntax while *not* borrowing Lean's
order-insensitivity.

### The index, and the values

`Record (fields : List (String × Type))` is both the index of a record-sorted term and the Lean
value such a term denotes — as `Set` and `TotalMap` are, which is what lets `Solver.getValue` answer
one. Its values are `Values fields`, a **computed** product (`gamma × Values rest`, ending in
`PUnit`) rather than a spine, and that is not a style choice: an inductive collecting one value per
field would have to bind a type variable per constructor and would land in `Type 1`, which `Env`
cannot answer. `Values` is `@[expose]`d because every instance below reduces it.

`FieldOf fields name gamma` is what makes a field access typed while still being written as a name:
the instances walk the list and the head match wins, so a name that is not there — or one asked for
at the wrong type — has no instance and does not compile. It carries **both** accessors a record
needs, because the two representations differ: a `Fin` **position** reaches a field's term, those
being held erased in an array, and a **projection** reaches a field's value, `Values` being a nested
product with nothing to index. The `Fin` is safe here in a way the one rejected for `Col` was not —
resolution produces it, so there is no numeral for `Fin`'s modular `OfNat` to reduce.

**A record carries data, so its `Ord`/`DecidableEq`/`Hashable` are real**, unlike the relation
indices' trivial ones: a `Set (Record …)` keyed by a constant order would collapse every record to
one. Each is lifted field by field through its own class — `OrdFields`, `DecidableEqFields`,
`HashableFields`, `ToStringFields` — deliberately separate so that a record demands of its fields
only what is asked of the record. A field whose type has no order, a function's for instance,
costs nothing until someone wants the record ordered.

### Terms

Sort-erased, everything goes through `Datatype`, and what the module adds is the three facts a
record guarantees plus the error messages that follow: there is exactly one constructor, so
`Srt.recordCtor` discharges the index; the constructor's name is cvc5's and never the way in, so
everything is keyed on field names; and a field's sort is known, so `Term.mkRecord` checks its
arguments itself rather than letting cvc5 report `[internal] bad type for constructor argument`
naming the mono-morphised sort.

```lean
Srt.recordCtor / recordFields
Term.mkRecord (srt) (fields : Array (String × Term))   -- by *name*, reordered into the sort's order
Term.mkRecordFrom (fields : Array (String × Option Srt × Term))   -- each field's sort stated or not
Term.recordGet / recordSet                             -- take the *term*; the sort comes off it
Fields names                                           -- one term per field, names in the type
```

`Fields` is where totality comes from: `fs.get "a"` answers a `Term`, never an `Option Term`,
because a name that is not there has no `FieldAt` instance. Sort-erased its index is the **names
alone** — a term carries no Lean type there, so types would buy nothing and would have to be written
out at every construction.

Typed, the index carries the field names *and* their types, so there is nothing to look up and
**no `Ctor`/`Field` handle** — the counterpart of the declared-datatype API simply has no reason to
exist. `Term.mkRecord` takes neither a sort nor field names, and `Term.recordFields` takes no names.
Fields in the wrong order, a field omitted, an unknown name and a field at the wrong type are all
compile errors where sort-erased they are cvc5 `[internal]` errors.

The value conversions read a record's **children**, not its selectors: a record value is an
`APPLY_CONSTRUCTOR` whose *first child is the constructor* and whose remaining children are the
fields in order. Getting that `.drop 1` wrong is silent until a field converter is handed the
constructor. Because it walks children, it works on a term that was merely *built*, as bags and
nullables do and sets and sequences do not.

### `smt!`

```lean
smt! {a := 7, b : boolSrt := true}   -- a field's sort stated or inferred, per field
smt! {r with a := 9}                 -- an update, chaining for several fields
smt! r.a                             -- projection
smt! f x |>.a                        -- Lean's pipeline projection
```

A stated sort can only *confirm*: sort-erased `Term.mkRecord` checks it while building the sort from
it, typed `Term.checkFieldSrt` checks it against the index. In both layers it may be written as a
Lean type or a `Srt` (`srtOf%`). There is **no syntax for the empty
record** — `,+` in the grammar rules it out. A field named twice in an update is refused as the
literal is expanded, since it would otherwise silently overwrite.

**Projection is two mechanisms, and has to be.** `r.a` reaches the expander as one identifier token,
so whether it names something or reads a field off something is a question about scope — which a
macro cannot ask. That leaf is a term *elaborator* (`smtProjU%`/`smtProjT%`), resolving in Lean's
order: a local head first, then the longest prefix that resolves. What is left over is read **by
type**, as Lean's dot notation does: while the value is not a term (`isSmtTermType`: a layer's
`Term`, `BVar` or `NT`), the next component is a Lean projection, and from the first term on the
rest are record fields. So `syms.steps` on a symbol structure is the Lean field, and `h.r.a`
projects `r` in Lean then reads record field `a`; splitting by name alone sent `vars.x` to
`recordGet`. A value whose type is unknown is read as a term, as before. Everything else in the DSL
stays a macro. A head that is *not* an identifier (`(f x).a`, `![e].a`, `{…}.a`) cannot be fused by
the lexer and so is an ordinary grammar rule; `smt! r .a`, with a space, is neither and does not
parse.

Two things the elaborator has to get right, both found by the unused-variable linter: an identifier
with **no** fields is passed through *unchanged*, since a rebuilt identifier is not a reference the
linter counts — getting this wrong made every identifier in `smt!` look unused; and the head of a
real projection is split with `Syntax.identComponents`, which is what Lean's own dot notation uses,
because it splits at the identifier's real source ranges. `mkIdentFrom` spanning the whole path is
not a reference, and `addTermInfo` by hand does not fix it. An identifier carrying macro scopes is
never split at all: it stands for one binding a macro introduced, not a path a user wrote.

`e |>.a` is Lean's `pipeProj` at Lean's precedence, **minimum**, so it takes everything to its left:
`a + b |>.c` is `(a + b).c`. That reading is nearly always a mistake here, an arithmetic term having
no fields, but it is a loud one, and matching the language is worth more than optimising for it.

## `Nullable` is Lean's `Option`

[Cvc/Untyped/Theory/Nullable.lean](Cvc/Untyped/Theory/Nullable.lean) and its typed twin. cvc5's
`Nullable` is the `Option` sort — a value is `nullable.null` or `nullable.some v` — and Lean's own
`Option` denotes it, so there is no new type in `Cvc/Types/`: `ToTyp (Option α)` sits in `Srt.lean`
beside `ToTyp (Array α)`, and core already supplies the `Ord` and `ToString` instances a container
element needs.

**It is a *structural* sort constructor, and that is the whole reason this works.** `Typ.nullable`
is an ordinary recursive case that `toSrt` rebuilds, exactly like `set` or `seq`; building the same
nullable sort twice gives the same sort. A declared datatype has no such property, which is why
`Typ.datatype` carries a name and goes through the registry. Adding the case meant touching `Typ`'s
`beq`/`beq_refl`/`eq_of_beq`/`toString`, `isArith`/`hasConcat`, `Typ.isFlat` and `toSrt`.

cvc5 implements it as a datatype underneath — one monomorphised per element sort, named
`__cvc5_nullable_Int` and so on, `isParametric` being false — and that surfaces in exactly one
place: a nullable **value** is an `APPLY_CONSTRUCTOR` term, so `getNullableElem?` reads it off the
term's kind and children, dispatching on the constructor's symbol (`nullable.null` versus
`nullable.some`). Unlike a set or a sequence, that works on a *built* term as well as on a model's
answer.

- **`mkNull` takes the element sort**, like every constructor of a polymorphic sort. cvc5's
  `mkNullableNull` wants the *nullable* sort — verified; passing `Int` fails with `expected nullable
  sort` — so `mkNull` builds it. Typed, the index supplies it and `mkNull` takes nothing.
- **`isNullableValue` is `Env Bool`**, not the pure `Bool` the other `is…Value` predicates are: it
  asks the term's sort, since nullable-sorted is necessary but not sufficient — a declared constant
  of nullable sort is not a value.
- The five constructors are hand-written. Four of them (`nullableSome`, `nullableVal`,
  `nullableIsNull`, `nullableIsSome`) are ordinary shape-typed operators that `op%` could generate
  once `Shape` gains a `nullable` case; `nullableNull` is a `tm` constructor with a free result
  variable, exactly `setEmpty`'s case. `mkNullableLift` is not wrapped at all — its `Kind` is a
  runtime argument, so no `Shape` describes it.

### Lifting operators over nullables

`Cvc/{Untyped,Typed}/Theory/Nullable/<Theory>.lean`, generated by `gen_untyped_nullable%` /
`gen_typed_nullable%` from the *same* `op%` entries as the plain constructors. Every liftable
operator gets a `<id>?` — `add?`, `addN?`, `lt?`, `toReal?` — whose signature is its counterpart's
with an `Option` around every argument and around the result, and nothing else changed:

```lean
add?  [ToTyp α] [IsArith α] : Term (Option α) → Term (Option α) → Env (Term (Option α))
addN? [ToTyp α] [IsArith α] : (terms : Terms (Option α)) → 2 ≤ terms.size → Env (Term (Option α))
lt?   [ToTyp α] [IsArith α] : Term (Option α) → Term (Option α) → Env (Term (Option Bool))
```

**Generating is what makes the guarantees hold.** Exposing `mkNullableLift`'s `Kind` to a caller
could not: cvc5 validates nothing there, and `mkNullableLift .NOT #[x, y]` builds the malformed
`(nullable.lift (lambda (a b) (not a b)) x y)` without complaint. Generating from the entry that
already records the arity and the n-ary form makes that unrepresentable, and `addN?` carries the
same `2 ≤ size` autoparam `addN` does.

The alternative — a lift taking the operator as a *function* — is a dead end, and the reason is
worth knowing on its own: **an autoparam'd function is not first-class.** Passing `Term.addN` as a
value makes Lean eta-expand it and run the autoparam tactic immediately, against an array it knows
nothing about, so it fails with `could not synthesize default value for parameter
'atLeastTwoElements'`. An explicit `fun ts h => Term.addN ts h` does elaborate, but nothing
point-free will. This affects both layers identically.

- **The lift is strict**, so `equal?` is a trap: it is *not* `Option`'s equality. `equal?` of two
  `none`s is `none`, not `some true`. That is `nullable.lift`'s semantics, not a choice.
- **What lifts** is `OpSpec.isLiftable`: no `tmFn`, no indices, no value parameters, at least one
  argument. Constructors have no argument to be null and build through a `TermManager` method;
  indexed operators are applied through an `Op`, and `mkNullableLift` takes a `Kind`. Value
  parameters only ever occur on constructors, so they rule nothing else out.
- **`Option (Option α)` needs no special case.** `add?` at `α := Option Int` demands
  `IsArith (Option Int)`, and no such instance exists.
- **No grammar is emitted.** `+` belongs to `add`; emitting again would declare the rule twice.
- The sort-erased body needs no sort at all — `mkNullableLift` takes only the kind and the terms —
  so it is shorter than the plain one, and the typed body is the usual delegation.
- One module per theory per layer, so importing `Nullable/Arith` compiles arithmetic alone. The
  lift module costs about what its plain counterpart costs.

`N'` variants are generated too, and **their unit is the plain one wrapped in `some`** — every
argument and the result of a lifted operator are nullable, so `addN'? #[]` is `some 0` and `mulN'?
#[]` is `some 1`. That is why a lift module **imports its plain theory**: the unit goes through that
theory's own constructor (`mkInt` here), which the lift module does not generate. As for plain
`addN'`, an empty array leaves the index undetermined and has to be ascribed.

On one term, an `N'` variant (plain or lifted) answers the term for an operation and the unit for a
relation — `equalN' #[t]` is `true`, `t` having the wrong sort (`OpSpec.unitOn1Default`). The typed
variants pass an arithmetic unit at the operands' sort (`arithUnitAt`: `addN' (#[] : Terms Rat)` is
`0.0`), the sort-erased ones having no sort to go by. `on0`/`on1` are built with `mkIdent`, so a
caller can pass them by name; hygienic, they could not be named at all.

Status: **every theory but `Fun`** — 205 liftable entries over eleven theories, one module each per
layer. Per-theory counts: BitVec 44, Arith 36, Float 26, String 26, Bag 18, Set 17, Seq 14, Regex 9,
Bool 8, FiniteField 4, Array 3. `Fun` is deliberately left out.

Only Arith and Bool actually have unit elements, so only they *need* the plain-theory import — but
every lift module takes it, so that adding a unit to a theory later cannot silently break it.

## Relations and tables

[Cvc/Types/Relation.lean](Cvc/Types/Relation.lean) and
`Cvc/{Untyped,Typed}/Theory/{Relation,Table}.lean`.

A relation is a **set of tuples** and a table a **bag of tuples**; neither is a sort of its own,
there being no `RELATION_SORT` or `TABLE_SORT`. Duplicates mattering is the whole difference, and
the two families are otherwise operator for operator identical. cvc5 marks all fifteen kinds
experimental.

**The index is list-shaped, not a product.** `Tup α β` is a tuple whose components are `α ++ [β]`,
`Rel α β` a set of them, `Tab α β` a bag. Splitting the last component off makes the list non-empty
*and* makes "the last component" a parameter position, so unification can find it: `?α ++ [?μ]`
against a concrete list is higher-order and Lean will not solve it, while `Tup ?α ?μ` against `Tup
[Int, Bool] Real` is first-order. That is what lets join be a signature rather than a type-level
program:

```lean
relJoin : Term (Rel α μ) → Term (Rel (μ :: α') β') → Env (Term (Rel (α ++ α') β'))
```

`++` and `reverse` survive only in *result* positions, where they are computed rather than matched.
`Rel [] α` is the unary relation, so `relIden`/`relJoinImage` need no one-tuple type. See "Tuples"
below for why the product index cannot do any of this.

The three index types carry no data, and their `DecidableEq`/`Ord`/`Hashable` are **written out
trivially rather than derived**: `deriving` constrains the phantom parameters even though nothing
uses them, which would demand `Ord β`, which not every component type has — a function's, for
instance. They exist only so a container
of them can be spelled — `relGroup` answers `Set (Rel α β)`.

**All fifteen kinds are wrapped in both layers.** Sort-erased they are hand-written, for the reason
tuples are: `Shape` has no product case, so `op%` cannot describe a set of tuples. The two indexed
joins take `Array (Nat × Nat)` rather than cvc5's interleaved index list, so the list cannot come
out of odd length.

**The set and bag operators are restated at these indices** — `relMember`, `relUnion`, `relCard`,
`tableCount`, `tableUnionMax`, the n-ary `relUnionN`/`relInterN`/`relMinusN` and
`tableUnionMaxN`/`tableUnionDisjointN`/`tableInterMinN`, and the rest — so working with a relation
or table never means leaving it. `bagSubbag` is restated as `tableSubtable`. `relToSet`/`relOfSet`
and `tableToBag`/`tableOfBag` are identities on terms, there for the four that genuinely leave:
`setMap`/`setFold`/`bagMap`/`bagFold`, whose results are arbitrary containers.

**The aggregates take their folding function as a term**, which `Term.lambda` builds — its two
arguments are a tuple of the relation and the accumulator, in that order. Typed, the accumulator's
index is fixed by `init` and the function's codomain together, so `relAggregate` answers a `Set
gamma` and `tableAggregate` a `Bag gamma`, not a container of tuples. Note cvc5 **loses the group
key**: the answer is one accumulator per group, so recovering the key means folding it into the
accumulator.

**Positions are typed.** `Col α β gamma` is a component's position carrying that component's type,
written as a numeral with `col%`; `Cols` is a `last`/`cons` spine of them that computes the index a
projection lands at. That is what makes `tupProject`/`relProject`/`tableProject` typed where cvc5's
`Array Nat` could only be sort-erased, and `Term.tupAt t col%2` reaches any single component — the
general form of `tupFst`/`tupLast`. A `Col` is `Ω`-free, so a column can be named at the top level
and reused.

- **`ColHead` is what lets a position be a numeral.** The two terminals — the head of `α` and the
  split-off `β` — have different types, so a macro expanding `col%2` cannot know which to emit; the
  class picks by the shape of `α`, and its two instances do not overlap. Out of range is then a
  type error, there being no instance left to end the chain.
- **Not a `Fin` position with a computed component type.** `Fin`'s `OfNat` reduces modulo the
  bound, so position `4` of a four-component tuple would silently become column *zero*, and every
  derived index would display unreduced. See [TODO.md](.notes/TODO.md).
- `col%` and `cols%` are `scoped` and declared at **maximum precedence**, so they need no
  parentheses as function arguments.
- A position is resolved by the shape of the component list, so an abstract tail —
  `Tup (Int :: αs) Rat` — has no `Col` past the concrete prefix. Generic code over an unknown shape
  stays sort-erased, through `T.relProject` on an `Array Nat`.

## Tuples

**There are two tuple encodings, and the newer one is better.** Not to be unified now, but worth
raising whenever a tuple-shaped problem turns up — it has resolved every one so far.

- **`α × β`**, the original. Right-flattening: `α × β × γ` is one three-component tuple. Used by
  `Term.mkTuple`, `Components`, `tupleProject`, `tupleSelect`, `fst`/`snd`, `OneTuple`.
- **`Tup α β`** in [Cvc/Types/Relation.lean](Cvc/Types/Relation.lean), whose components are
  `α ++ [β]` — a genuine list, with the last element split off. Used by the relation and table APIs.

The product encoding has no terminator, so the slot for "rest of the tuple" and the slot for "last
component" are the same one. That single ambiguity causes everything the tuple API cannot do:

- `α × β × (γ × δ)` collapses to four components — a nested tuple in last position is
  inexpressible, which is what `Typ.isFlat` and `Components.last`'s side condition exist to police;
- a *middle* component has no typed selector;
- `init`/`reverse` on the components need a type-level recursion whose base case is "α is not a
  product" — undecidable by instance resolution.

`Tup α β` dissolves all three, and the reason is **unification, not expressiveness** (see above).
That is why `relJoin`'s drop-last/drop-first is a signature rather than a program, why `Rel [] α`
needs no `OneTuple`, and why `tupFst`/`tupLast` are one-liners (`α.length` is a real runtime value,
`List Type` being a genuine list).

The middle-component gap is **closed on the `Tup` side and still open on the product side**, which
is the sharpest illustration of the difference. Nothing analogous to `Col` works for `α × β`: a
position there has to walk a right-nested product whose base case is "not a product", which is the
undecidable test above. The list has a terminator and the product does not.

Migrating would retire `Typ.isFlat`, `Srt.prod`'s flattening and `OneTuple`, and touch about six
library files plus four test files. Not done because the product encoding reads better in the common
two-component case and the churn is not yet paid for.

A tuple is indexed by a Lean **product**, and products flatten to the right exactly as function
sorts curry: `α × β × γ` is one three-component tuple, `(α × β) × γ` the two-component one whose
first component is a tuple. `Srt.prod` in [Cvc/Types/Tuple.lean](Cvc/Types/Tuple.lean) is what
flattens, and it is `@[expose]`d so the typed constructor's check can reduce downstream.

That flattening constrains the typed constructor, which is why `Term.mkTuple` takes a `Components`
spine rather than two terms. A tuple's components are held flat because the sort is flat, and
`Components.last`/`cons` are the only builders, so the term count and the index stay in step. The
one case the index cannot describe is a **product as the last component**: its components would
flatten into the tuple being built while the single term standing for it would not, so `last`
carries an autoparam over `Typ.isFlat` that rejects it at elaboration time. Any other position is
fine, since a tuple there nests. Generic code over an unknown last component has to pass that proof
explicitly — there is no class for it.

`tupleProject` answers a *tuple*, not a component: projecting one index gives a one-component tuple.
Its result is sort-erased in the typed layer, since which components an index array selects is a
runtime value.

## Function sorts, lambdas and application

A function-sorted term is indexed by a **Lean arrow**: `Shape.fn` renders to `dom → cod`, and
`instance [ToTyp α] [ToTyp β] : ToTyp (α → β)` in [Cvc/Srt.lean](Cvc/Srt.lean) is what gives it a
sort. `op%` still writes the shape `fn α β`. Function sorts are **curried**: `α → β → γ` is `(-> α β
γ)`, because `Typ.toSrt`'s `foldFunctionCod` flattens the right-nested spine into cvc5's n-ary
domain, while a function in *domain* position stays nested and is genuinely higher-order. Because
the index is an ordinary arrow, a `Solver.defineFun` result — whose index `BVars.signatureTo` builds
as arrows — applies directly, with no re-typing.

`Cvc/{Untyped,Typed}/Core/BVar.lean` hold `BVar.lambda`, `BVars.lambda` — typed, answering
`Term (bvs.signatureTo β)` — and `Term.lambda`/`lambda1`.

**`Term.lambdaH` is the HOAS spelling**, the body a Lean function of the variables as for
`forallH`. Sort-erased it takes the sorts beside the names, through the quantifiers' `Binder`.
Typed it goes through `LambdaBinder φ σ`, whose `σ` is an **`outParam`** computed from the function
type — `Term α → … → Env (Term β)` gives `α → … → β` — so `lambdaH fun (x y : Term Int) => …`
answers a `Term (Int → Int → Int)` with nothing written but the binders. A body against the wrong
expected index is reported as a missing `LambdaBinder (…) (wrong σ)` instance, pinned in the typed
`Core/BVar` test. `smt! fun (x y : s) => body` expands to it in both layers. Applying a lambda
builds an `APPLY_UF` that cvc5 prints as `@`, and it is reduced even under a first-order logic:
`(fun (x : Int) => x + 1) 2 = 3` is sat in `QF_LIA`.

**`BVar` is in `Core` because every view needs it.** A term view's aggregate has a `bvar` leaf
whatever theories are imported, so `def.term_view` over `Core` alone has to find `BVar` and
`Term.asBVar`. It depends on `Core.Value` and not on `Core.Bool`: `Bool` is a view-generation site
importing `Core.View`, which imports `BVar`, so the other way round is a cycle. `Solver` publicly
imports `Core.Bool` itself, which it used to get through `BVar`, and which `Symbols` relies on.

**A signature is shown in the form it computes to**, by a delaborator beside `signatureTo`. Without
it a `Grammar` or a synthesized function displays as its `BVars.signatureTo` application, where
`Grammar (Int → Int → Int)` is what a reader wants; being an `abbrev` does not help — reducibility
governs unification, not printing, and Lean shows a type as inferred rather than in normal form.
Three details are
load-bearing and are commented at the definition: the first `guard` stops a signature that *cannot*
reduce, over a variable spine, from delaborating to itself forever; it compares the whole
expression rather than its head, which is what lets a partly concrete spine show how far it got;
and the reduction is shown only when it has **no metavariables** left in it, because
mid-elaboration — a hover inside a `do` block, before the pushed variables' types are solved —
`?m → ?m → Int` says less than the application it came from, that one at least naming the
variables. `instantiateMVars` runs first, so an *assigned* metavariable resolves rather than
suppressing the reduction. The three reducible cases are pinned in
`CvcTests/Typed/Core/BVar.lean`; the metavariable case only arises mid-elaboration and so cannot
be pinned by a build.

**`BVars` collects in reverse**:
`BVars.push acc (BVars.push t [])` is the lambda `t → acc → _`, which is the order `signatureTo`
folds and the order `erase` restores. Getting it backwards silently reverses the parameters.

`Cvc/{Untyped,Typed}/Theory/Fun.lean` hold application. `applyHo` (`HO_APPLY`, one argument at a
time) is kept and is genuinely different — it does require a higher-order logic. Everything else is
`APPLY_UF`.

**`applyN` flattens.** When the function term is itself an `APPLY_UF`, its children are spliced
rather than nested, so all four spellings — `applyN`, `apply3`, a `CoeFun` chain, stepwise `apply2
(apply f i) b r` — build the identical flat `(f i b r)`. That is what keeps ordinary
uninterpreted-function application out of the `HO_` logics: a nested application would leave a
function-sorted intermediate, which cvc5 rejects with `Function terms are only supported with
higher-order logic`. So the fixed-arity `apply`/`apply2`/`apply3` are hand-written on top of
`applyN` in both layers, and [Cvc/Spec/Fun.lean](Cvc/Spec/Fun.lean) specifies **only** `applyHo`.

Typed, `applyN` takes an `Args φ β` spine (`last`/`cons`, so non-emptiness is structural and the
arity is not capped at three). Stopping the spine early is a partial application, and the index it
computes is the sort cvc5 gives. Two `CoeFun` instances — on `Term (α → β)` and on `Env (Term (α →
β))` — let `f a b` be written directly, the second being what makes a chain need no parentheses.

Note `setMap` needs `Ord` on the codomain as well as the element, since the result set is keyed by
it — mapping a set into a function type, which has no `Ord`, is therefore not expressible. Folds
have no such constraint: their accumulator never keys a container. `Rat` has an `Ord` because
`Srt.lean` declares one, core providing none; it is at low priority so that Mathlib's wins where
both are present.

Nested containers work because [Cvc/Types/](Cvc/Types/) provides `Ord` instances. That is what makes
`bagPartition : (α → α → Bool) → Bag α → Bag (Bag α)` expressible: `Shape.ordVars` only constrains
type *variables*, so the generator emits `[Ord α]` and instance resolution supplies `Ord (Bag α)`
for the result's outer layer.

## Symbols

`Cvc/{Untyped,Typed}/Core/Symbols.lean`, **both layers**. A user record is written once as
`MySymbols (W : Symbols.Wrap)`, and `Symbols.Sig` instantiates the same record at identifiers
(`fun _α => String`), at terms (`𝕂 Term` sort-erased, `Typed.Term ·` typed) and at values
(`fun α => α`), with `Wrap` carrying the `ToTyp`/`TermToValue` constraints, over a `Symbols` class
supplying `mapM` and `foldM`.

**`foldM` is a class field, beside `mapM`**, visiting the symbols in field order with a state, in
any monad. `structure.symbols` defines it directly, as a chain of binds over the fields
(`Ext.foldChain`); the field's default derives it from `mapM` through `StateT`, so a hand-written
instance need not define it. `Idents.foldM`, `Terms.foldM` and `Values.foldM` reach it under dot
notation — typed, `Terms.foldM` hands each symbol over at its own index, `Term α`. Those three pass
the wrap explicitly and eta-expand `f`, binding its instances: left to inference, the wrap stays a
metavariable and `TermToValue ?α` is stuck. Sort-erased, `foldM` takes `[Ω]` exactly as `mapM`
does, so folding identifiers or values there needs a scope; typed, neither takes one.

**`Ω` is taken only where a term is actually mentioned**, and that is what makes the API usable
from outside a scope. `Wrap` takes none, so `Sig.Idents` and `Sig.Values` take none either — only
`Sig.Terms [Ω]` does, along with the constraint aliases, `mapM`, `declare`/`declareIn`,
`getValues` and `findCex`. So a caller can name a symbol structure's identifiers and its *values*
outside `Env.run` and only enter a scope to do the solving, which is exactly the shape of the
worked examples:

```lean
def run [S : Symbols Syms] (symbols : Syms.Idents) (constraints : [Ω] → Array (String × Syms.Fun))
: BaseIO (Result S)
```

**A constraint is a function into `Env`, at one scope.** `Sig.Fun [Ω]` is `sig.Terms → Env Term`
sort-erased and `sig.Terms → Env (Term α)` typed, with `Sig.Pred := sig.Fun Bool` typed. The scope
is a *binder* of the alias, not part of the type, so the aliases are in `Type` and a `Sys` holding
them can be returned through `Env`; code written once for every scope says so at its own boundary,
as `run` does with `[Ω] → Array …`. A top-level constraint therefore needs `variable [Ω]`.

**The aliases are spelled on the signature, never on the instance.** `Symbols` `export`s the `Sig`
aliases, so `Symbols.Idents` is `Symbols.Sig.Idents` and takes the *signature*: `Syms.Idents`
works, and `S.Idents` with `S : Symbols Syms` does not — dot notation finds no `Symbols` argument
to put `S` in. A signature quantifying over the instance writes `[S : Symbols Syms]` and
`Syms.Idents`, as `run` does.

**A symbol structure's whole obligation is the `Symbols` instance.** Everything else is generic
over the `Sig` and needs no per-structure definition: `Idents.declare`/`declareIn`,
`Terms.getValues` (in `EnvSat`) and `Terms.findCex`, which is `checkSat?` with `getValues` in its
sat branch.

### Symbols at a step

What used to be a separate state-variable framework is part of `Symbols`. `Symbols.At k W α` wraps
a field read at step `k`, `get` unwraps it, and the step-indexed instantiations are `TermsAt k`,
`ValuesAt k` and `ValueTermsAt k`. `Idents.declareAt`/`declareAtIn` declare a step's symbols, and
the constraint aliases come in step forms too: `FunAt k`, `Fun2At k k'` (`k'` defaulting to
`k + 1`) and their primed forms quantifying over the steps, plus typed `PredAt`/`RelAt`.
`Cvc/{Untyped,Typed}/Extra/Sys.lean` builds transition systems and bounded model checking on top,
with `Sys.Trace` for a counterexample.

- **In `smt!`, a state symbol needs no `get`.** Sort-erased its `CoeDep` to the term fires, the
  target being the index-free `Term`. Typed it would target `Term ?α` and stay stuck in `x + y`
  over two symbols, so `Ext.typedToTerm?` unwraps a `Symbols.At` by its type, as it does an `NT`
  or a `BVar`. Outside `smt!`, write `.get`: `values.count.get`.
- **A step's symbols are named for it**, `count__@__k`, in both layers — the typed `declareAt`
  names them through the sort-erased `Sig.mkSymbolIdentAt` rather than restating the convention.
  That is what lets a model or an error say which step a variable belongs to; relying on
  `declareFun`'s `fresh := true` alone would keep the terms distinct while printing every step
  under the same name.

### `structure.symbols`

The instance is what `structure.symbols` generates, so an ordinary symbol structure is written with
no boilerplate at all:

```lean
structure.symbols MySymbols where
  /-- Whether the thing is on. -/
  isOn : Bool
  count : Int
```

The user writes plain Lean types and never mentions the `Wrap`; what is emitted is the structure
the class wants — `(W : Symbols.Wrap)` added, every field's type wrapped in it — an `idents`
**value** naming each symbol after its field, the instance built on it, and one alias per
`Symbols.Sig` type. Doc comments, on the structure and on each field, are carried through.

**The aliases are a list, per layer.** `Ext.symbolsSharedAliases` holds the ones both layers have
(`Idents`, `Values`, `ValuesAt`, `Terms`, `TermsAt`, `BVars`, `ValueTerms`, `ValueTermsAt`), and
each layer passes its own on top — `Fun`, `FunAt`, `Fun2At` and their primed forms sort-erased, and
typed `Pred`, `PredAt`, `RelAt` and theirs besides. Each entry says whether the alias takes the
scope, and is emitted as `abbrev MySymbols.X [Ω]? := @Symbols.Sig.X _? MySymbols`. The `@` is
load-bearing: plain application would fill `Fun2At`'s optional `k'` with its default inside the
alias, and `MySymbols.Fun2At 0 5` could no longer be written. Adding a `Sig` type means adding its
name to one list. `CvcTests/SymbolsAliases.lean` pins every alias's signature, with no `Ω` in scope.

`Cvc/Gen/Symbols.lean` holds what both layers share; each layer declares its own `scoped` spelling,
so `open Cvc.Untyped` selects the sort-erased one exactly as it selects `smt!`.

Things to know before touching it:

- **`structure.symbols` is one token, and that is not cosmetic.** A `scoped` command whose leading
  token is *not* reserved never activates — Lean's command parser dispatches on the leading token,
  and an identifier-leading scoped parser is never found, so `&"symbols"` parses at the declaration
  and matches nothing at the use site. Spelling the command `symbols structure` would therefore
  make `symbols` a global keyword, which broke a hand-written example binding `mapM symbols f`.
  Folding it into one punctuated token keeps `symbols` an ordinary identifier.
- **A quotation cannot splice a variable number of fields into a structure.** `structFields` is a
  `manyIndent`, and an antiquotation there is read as one field's *name*, so the structure is
  assembled node by node in `Ext.mkSymbolsStructure`. Two shapes are easy to get wrong and fail
  obscurely: `structFields` holds its binders in a null node rather than as direct children, and
  `declModifiers`' first slot is a null node holding the doc comment, empty when there is none.
- **A field is rebuilt from its own node**, with only its type replaced, so the writer's doc
  comment, name and source position survive untouched.
- What it refuses: a field named as something generated beside the structure — any of that layer's
  aliases, `idents`, `mapM`, `foldM`, `declare`, … (so `PredAt` is a legal field sort-erased and not
  typed) — a field with parameters or without a type, and `extends`, which the grammar has no slot
  for.
- What it cannot express, and what the hand-written path is still for: a field that is a
  *collection* of symbols (`Array (W Bool)`), and an `InitData` other than the default `Unit` —
  both shown by the second example in each file.

Worked examples live with the tests rather than in the module: `CvcTests/{Untyped,Typed}/`
`Symbols.lean` cover both paths, the generated one and the hand-written one, plus symbols at a
step, and the module docstring points at them. `import all Cvc.Untyped.Core.Solver` is
load-bearing in the sort-erased module, because `Terms.getValues` runs an `Env` action inside an
`EnvSat` block and that lift is private to the solver module; the typed module needs no such thing.

## Code-generation macros (read these before editing wrappers)

| macro | file | purpose |
|---|---|---|
| `enum_def% Id ← cvc5.Enum \| variant ← SRC_VARIANT …` | [Cvc/Basic.lean](Cvc/Basic.lean) | mirror a cvc5 enum as a Lean inductive + `ofUnsafe`/`toUnsafe` + round-trip theorems + `example : … := rfl` per variant |
| `def0%`/`def1%`/`def2%`/`def3% Id ← cvc5.Ty` | [Cvc/Defs.lean](Cvc/Defs.lean) | zero-cost newtype over a cvc5 type; levels add `ToString` (1), `BEq`/`Hashable` (2), `Ord`/`LT`/`LE`/`compare` (3). An optional `(ofId / toId)` suffix renames the conversions. A leading doc comment documents the type; without one it gets `@[inherit_doc cvc5.Ty]`, which a downstream `module` (verso's `{docstring}` included) sees only under `import all cvc5` |
| `is%` / `get%` | [Cvc/Srt.lean](Cvc/Srt.lean) | the 28 sort testers; the accessors in both the failing and the `?` form |
| `op% id sig := KIND …` | [Cvc/Spec/Decl.lean](Cvc/Spec/Decl.lean) | register one operator's specification |
| `gen_untyped%` / `gen_typed%` (`from <Spec module>`) | [Cvc/Gen/Term.lean](Cvc/Gen/Term.lean) | emit a theory's constructors into the current layer, plus the DSL grammar (untyped only) |
| `gen_untyped_nullable%` / `gen_typed_nullable%` | [Cvc/Gen/Term.lean](Cvc/Gen/Term.lean) | emit the `<id>?` lifts of a theory's liftable entries |
| `env_gen% EnvXT / EnvX` | [Cvc/Gen/SolverMode.lean](Cvc/Gen/SolverMode.lean) | monad instances + a module-private lift for a mode monad |
| `def%` | [Cvc/Srt.lean](Cvc/Srt.lean), [Cvc/Typed/Core/Solver.lean](Cvc/Typed/Core/Solver.lean) | define a wrapper carrying `@[inherit_doc]`; on the typed side, re-type a sort-erased function |
| `structure.symbols Id where …` | [Cvc/Gen/Symbols.lean](Cvc/Gen/Symbols.lean) | a symbol structure, one alias per `Symbols.Sig` type (the list differs per layer) and its `Symbols` instance |
| `smt.grammar! s (x : T) where nt : T := alt \| …` | [Cvc/Untyped/Grammar.lean](Cvc/Untyped/Grammar.lean) | a grammar as one BNF-style block; `scoped` per layer, expanding to `grammarU!`/`grammarT!` |
| `smt.mkGrammar! …` / `smt.letGrammar! g ← …` | [Cvc/Untyped/Grammar.lean](Cvc/Untyped/Grammar.lean) | the same block, also answering (resp. binding, as a `do` element) its parameters and non-terminals |
| `regex! "a" ['0'-'9']+ \| …` | [Cvc/Untyped/Theory/Regex.lean](Cvc/Untyped/Theory/Regex.lean) | a regex in the usual notation; `scoped` per layer, expanding to `regexU!`/`regexT!` |
| `gen_untyped_view%` / `gen_typed_view%` (`from <Spec module>`) | [Cvc/Gen/View.lean](Cvc/Gen/View.lean), [Cvc/Gen/TypedView.lean](Cvc/Gen/TypedView.lean) | emit and register a theory's view |
| `register_untyped_view%` / `register_typed_view% <View> [ctor KIND, …]` | same | register a hand-written view |
| `def.term_view V` | same; `scoped` per layer over `def.untyped_term_view` / `def.typed_term_view` | the aggregate view of every imported theory, its abbreviations, `V.of` and its `TermView`/`ViewFamily` instance |
| `srtOf% e` | [Cvc/Srt.lean](Cvc/Srt.lean) | a term elaborator: `Srt.of e` for a Lean type, `pure e` for a `Srt` — how the DSL accepts either |
| `smtExpand% <layer> <smtTerm>` | [Cvc/Ext.lean](Cvc/Ext.lean) | the DSL's dispatch: a `macro_rules` table each theory adds its own forms to, and what `smt!`'s recursion goes through |

## Documentation style (follow this exactly)

- **Line-wrap everything at 100 characters** — docstrings, `/-! … -/` module docs, and ordinary
  comments alike. This is the width the whole codebase uses.
- **A docstring opens with a single summary line that does not wrap.** If there is more to say, put
  a blank line after that first line, then the rest as paragraphs/sections:

  ```lean
  /-- Type variables that need an `Ord` instance, because they index a `Set`, `Bag` or `TotalMap`.

  `Set`, `Bag` and `TotalMap` are `Std.TreeSet`/`Std.TreeMap` wrappers, so their element
  (respectively index) type must be ordered.
  -/
  def ordVars : Shape → Array Name := …
  ```

  A one-line docstring stays on one line: `/-- Binary conjunction. -/`.
- The closing `-/` of a multi-paragraph docstring goes on its own line.
- **Exception**: `#guard_msgs` expected-output docstrings are compared verbatim against Lean's own
  message rendering, so they keep whatever wrapping Lean produces even past 100 columns. Never
  reflow them.
- **Never reference a markdown file from Lean source.** Not from a docstring, not from a `/-! … -/`
  module doc, not from an ordinary comment — and never as a markdown link, which does not even
  render in generated documentation. `CLAUDE.md` and the notes under `.notes/` (`MISSING.md`,
  `TODO.md`, `Cvc5Issues.md`, `LeanIssues.md`, `CvcLeanIssues.md`) are notes *about* the project;
  the source is the project, it is what users read, and it must stand on its own. Say the fact
  instead of pointing at where it is written down: "cvc5 answers a segfault here, which is a cvc5
  bug" rather than "see `Cvc5Issues.md`". Cross-referencing another *Lean* declaration or module is
  fine, spelled as a name (`Cvc.Untyped.Theory.Sep`), not as a link.

## Conventions

- `private def toUnsafe` / `private def ofUnsafe` are the universal names for conversions to/from
  lean-cvc5 types. Modules that need them do `import all <Module>`.
- **Declare syntax categories with `(behavior := symbol)`** unless you specifically want the
  leading identifiers reserved. `declare_syntax_cat foo` turns every identifier-shaped atom of
  `foo` into a global keyword, which then shadows ordinary uses of that name (field names,
  variables) in every downstream module. `smtTerm` is the deliberate exception, see above.
- Size/non-emptiness side conditions are **autoparams** with a custom failure message, e.g. `(h : 2
  ≤ terms.size := by (try grind) <;> fail "failed to prove …")`. Proofs are done with `grind`.
- `@[inherit_doc <cvc5 decl>]` on wrappers so docs flow through from lean-cvc5.
- Wrapper types are `def`s equal to the underlying cvc5 type (`def Solver [Ω] := cvc5.Solver`), so
  the whole API is zero-cost; instances are `inferInstanceAs`.
- **Argument order follows cvc5, not readability.** `setInsert` and `bagCount` take the *element*
  first and the container last, because that is what `SET_INSERT`/`BAG_COUNT` want; calling them the
  other way round fails at runtime with `[internal] inserting into a non-set`.

### "null" means two unrelated things in cvc5

Read the word carefully before deciding whether something is in scope, because the two senses sit
next to each other in the same namespaces and sometimes in near-identical names.

- **The null pointer** — a null *object*, the uninitialised value of a wrapper type.
  `Term.isNull`, `Sort.isNull`, `Grammar.isNull`, `Datatype.isNull`, `SynthResult.isNull`, and
  the `null ()` constructors. **Do not port these.** This API never hands out a null object, so
  the check has nothing to answer. An absent `isNull` is the policy, not a gap in coverage.
- **A datatype's null value** — cvc5's `Nullable` sort, which is `Option`. `Srt.nullable`,
  `Srt.isNullable`, `Srt.getNullableElementSort`, and the term constructors `mkNullableNull`,
  `mkNullableSome`, `mkNullableVal`, `mkNullableIsNull`, `mkNullableIsSome`, `mkNullableLift`.
  **These are in scope.** They are a *container*, not a declared datatype.

`Srt.isNull` and `Srt.isNullable` differ by two letters and are the two different senses.
`mkNullableIsNull` is the *second* sense despite reading like the first: it builds a term asking
whether an `Option` value is `none`.

**Where nulls can come from, and how each is closed.** Audited: nothing in `Term` or `Sort` is
documented or observed to return one, and the `?` accessors cannot smuggle one — `extern_def!?`
builds the `?` form *from* the `Except` form, so it is `none` on error, never `some null`.

- **The documented null answers** are the interpolant, abduct and find-synth families, and every
  wrapper of them answers an `Option`, `none` for the null term: `getInterpolant`,
  `getNextInterpolant`, `getAbduct`, `getNextAbduct`, `findSynth`, `findSynthNext`, typed
  `findAnySynth`. `qeDisjunct` does too, though cvc5 documents no null answer for it. Plain `qe`
  stays a `Term`, cvc5 documenting no null answer for it either.
- **Each such `Option`-answering function has a `!` twin** answering the term itself and failing
  with a user error on `none` — `getInterpolant!`, `findSynth!`, `qeDisjunct!` — through
  `someOrThrowUser` in `Basic/Error.lean`, so the two cannot disagree. This is a second meaning of
  `!` beside the unchecked modal twins under "The solver"; both mark the form that can fail where
  its counterpart could not.
- **Proofs.** lean-cvc5's `Proof.null` and its null-backed `Inhabited cvc5.Proof` are the only null
  proofs there are, and neither is reachable: `Solver.Proof` is a `def` in both layers, which
  instance resolution does not unfold, so `proofs[0]!` does not compile (pinned in both `Proof`
  tests). `getProof` and `getChildren` build proofs from cvc5's proof nodes, never null, and the
  tests walk every step of every component through every accessor.
- **`Inhabited`.** Every *wrapped* type is clean — all ten reject `inferInstance`, because
  `def0%`–`def3%` deliberately emit no `Inhabited` where cvc5 has null-backed ones for eight of its
  types. That absence is load-bearing: it is why `terms[i]!` does not compile and why no
  `Array.get!`/`getD` can conjure a null term. A `def` over a wrapped type must not derive
  `Inhabited` either: under `import all` the derivation sees through to lean-cvc5's null-backed
  instance. `Untyped.BVar` did, so `(default : BVar)` and an out-of-range `bvs[i]!` were the null
  term; nothing used it, and it is gone.
- **lean-cvc5's `!` panic variants** return the null `default` after panicking. The library calls
  one, `Proof.getRewriteRule!`, which answers an enum, under a hypothesis that rules the panic out.
- **TODO: `Op` leaks a null through `Inhabited`.** `Defs.lean` does `export cvc5 (Kind SortKind
  Op)`, so `Op` keeps cvc5's `instance : Inhabited Op := ⟨null ()⟩` and `(default : Op)` is null.
  Low severity for now, since an `Op` is only consumed by `mkTermOfOp`, which the library never
  exposes. Fix by wrapping `Op` or not exporting it.

## Tests

The test library is Lean lib `cvcTests`, globbed with `Glob.submodules` over **both**
[CvcTests/](CvcTests/) and [CvcExamples/](CvcExamples/), with `testDriver = "cvcTests"` — so
`lake test` builds every module under either and nothing else. The examples are therefore tests:
a worked example that stops compiling, or whose `#guard_msgs` output drifts, fails the suite.

Adding a file to either tree is enough to have it run — **there is no aggregator to keep in sync**,
and no root `CvcTests.lean`: no target would build one, so its import list could only rot.

`lake test` is the way in. A single module can be built directly — `lake build
CvcTests.Untyped.Theory.Set` — but the library *root* cannot be: the package sets
`precompileModules`, so building the root of a precompiled library as a target tries to load the
very library it belongs to, and fails with `error loading plugin, initializer not found`.

Tests are plain `#guard_msgs`: `#guard_msgs in #eval Env.runIO do …` for behaviour, with the
expected output in the docstring **above**, and `#guard_msgs in example …` to pin an *expected*
elaboration error verbatim. There is no assertion harness.

- `CvcTests/Signatures.lean` — pins generated signatures of both layers, plus the definitional facts
  (`bvConcat`'s size arithmetic, `neg`'s generality over `IsArith`, the `Ord` binders derived from
  container shapes).
- `CvcTests/Fun.lean` — function sorts: that currying flattens while a higher-order domain stays
  nested, that signatures track the index through application (including *partial* application,
  which yields a function-indexed term), and that the `Ord` binders come out right.
- `CvcTests/Srt.lean`, `CvcTests/Logic.lean` — the sort layer and the SMT-LIB logic builder.
- `CvcTests/Scope.lean` — that `Ω` keeps scopes apart statically: a sort cannot leave its run,
  cannot escape into an enclosing run, and cannot meet a sort of another open scope.
- `CvcTests/Conversions.lean` — the signature of every typed/sort-erased conversion and alias, so
  a missing alias or an index turned implicit fails; plus the spines going down, solver and proof
  round trips, and a type given sort-erased value conversions alone used typed. Each type's checked
  conversions (a wrong sort refused) are tested beside that type.
**The test tree mirrors the source tree**, `Core`/`Theory` split included, so a module's tests sit
where the module does. Namespaces inside the test files were *not* renamed with it, nor when the
tree moved out of `Cvc/` to the root: `CvcTests/Untyped/Theory/Set.lean` still opens
`namespace Cvc.Tests.Untyped.Term.Set`, matching the namespace under test rather than its own path.

- `CvcTests/{Untyped,Typed}/Core/Bool.lean` — the one theory `Core` still holds.
- `CvcTests/{Untyped,Typed}/Theory/*.lean` — one module per theory per layer. The `Fun` ones
  additionally solve end to end: an uninterpreted function is declared, constrained and read back
  out of a model, plus functionality and congruence as unsat checks.
- **The DSL's tests mirror the DSL's layout.** A theory's notation is declared beside that
  theory's constructors, so it is tested beside them too: `∧`/`ite`/`true` in `Core/Bool`,
  arithmetic and the numeric literals in `Theory/Arith`, `&&&`/`|||`/… in `Theory/BitVec`, `∪`/`∈`
  in `Theory/Set`, `++` in `Theory/Seq`, `⊎` in `Theory/Bag`, string literals in `Theory/String`,
  `match` in `Theory/Datatype`, and `{a := t}`/`{r with …}`/`r.a`/`|>.` in `Theory/Record`. Typed,
  each of those also pins the *index* its expansion produces.
- `CvcTests/{Untyped,Typed}/Theory/Ext.lean` — what is left is what `Cvc/Ext.lean` itself declares:
  parentheses, the `![…]` escape, identifiers, application and `let`. Roughly a hundred lines each,
  depending on no theory.
- `CvcTests/{Untyped,Typed}/Theory/Quant.lean` — both spellings building the same formula, solving
  over quantified formulas, `qe`/`qeDisjunct` on them, and `smt! ∀`/`∃`; typed, the compile-time
  rejections (no variable, a non-formula body, a variable at the wrong sort).
- `CvcTests/{Untyped,Typed}/Grammar.lean` — grammars and the three `smt.grammar!` forms.
- `CvcTests/{Untyped,Typed}/Synth.lean` — synthesis, `checkSynth`'s branches, and `findSynth`
  over a two-term grammar: `some`, `some`, then `none` where cvc5 answers the null term, with the
  `!` forms failing there instead. Without a grammar `findSynth` uses the last `synthFun`'s, and
  cvc5 refuses when that `synthFun` was given none.
- `CvcTests/{Untyped,Typed}/Theory/{Datatype,Sep,Record}.lean` — the theories that are
  not term constructors alone. The `Record` ones cover the sort's reflection, every rejection's
  message, the `Fields` spine, and (typed) the Lean-value conversions.
- `CvcTests/{Untyped,Typed}/Value.lean` — the value round trip: every scalar instance, the
  containers (through a model where a built term is not a value), nesting, a size mismatch rejected
  rather than truncated, reading a model, and the introspection accessors.
- `CvcTests/{Untyped,Typed}/Core/BVar.lean` — bound variables and the definition functions that
  consume them: `mkBVar` freshness, that `BVar` stays distinct from `Term` with `toTerm` as the
  only way across, `Solver.declareFun` splitting a function index into domain and codomain, and
  `Solver.defineFun` over a `BVars` list at zero, one, two and three parameters — the two- and
  three-parameter cases with non-commutative bodies, so a reversed argument order would show.
- `CvcTests/{Untyped,Typed}/{Solver,Proof,Subst}.lean` — the driving surface. The sort-erased
  `Solver` test covers recursive definitions: `defineFunRec`, `defineFunRecTerm`, mutual
  `defineFunsRec`, `global` across `pop`. A sat answer over one needs `fmf-fun` (`unknown`
  without), which enforces a definition only on the applications assertions mention, so values are
  read off asserted equations — `getValue` of an unconstrained `fact 5` answered `1`. The `Proof`
  tests also cover inspection: each step's view of a refutation through arithmetic, congruence and
  rewriting (pinning which rules come out `other`), sharing, early exit, folding in `Env`,
  `foldUp` (a rebuild giving up through `Except`), the queries, the `theoryLemmas` component, and
  that every step of every component answers; typed, the view's indices and that a typed proof is
  refused by a sort-erased function.
- `CvcTests/ProofRules.lean` — one small problem per decoded rule the other proof tests do not
  meet, each step shown as both layers decode it, so a layout cvc5 changes shows up as a diff.
- `CvcTests/{Untyped,Typed}/View.lean` — the aggregate's signatures, taking terms apart, kind
  ownership; typed, the record/tuple/nullable helpers, wrong-sort matches as errors, containers
  denoting their own types. `CvcTests/View.lean` — the two `View` modules alone, with no theory.
- `CvcTests/{Untyped,Typed}/Traverse.lean` — folds, walks (bottom-up, top-down with revisit, `stop`,
  a refused replacement) and the zipper by hand; typed, a wrong-sort replacement as an error.

## What is left

[MISSING.md](.notes/MISSING.md) tracks the **API-surface** gap against lean-cvc5, area by area, with
the scripts that regenerate its counts. **Keep it updated as things land.** This section is the
different list: the library's own design work, ordered by dependency.

[TODO.md](.notes/TODO.md) is a third list — designs worked out far enough to be worth keeping and
then deliberately not started, so neither a gap nor a plan. A **SQL API over relations and tables**
is the entry there.

[Cvc5Issues.md](.notes/Cvc5Issues.md) is a fourth, and is about cvc5 rather than about this library:
problems found in the **C++ API** itself, each with a standalone C++ reproduction. Anything a
wrapper has to work around belongs there, with the workaround pointing back at it.

[LeanIssues.md](.notes/LeanIssues.md) is its Lean counterpart: sharp edges in Lean itself, each with
a standalone Lake reproduction, and the action to take upstream. Its first entry is the "not
unfolded because their definition is not exposed" note every typed sort error carries — pending a
post on the Lean Zulip. Rewriting the phantom types as structures to avoid it is ruled out.

[CvcLeanIssues.md](.notes/CvcLeanIssues.md) is about this library again, from the outside: drafts
of issues to open on cvc.lean's own repository, each written to be pasted as is. Windows CI is the
first.

Term construction and the solver are done — every theory is covered, and the solver is at parity
with lean-cvc5. What follows is everything that is *not* term construction or solver driving:

1. **`smt!` DSL parity** — the fixed forms the expander still lacks: the `name` literal for
   `mkSymbol`, a sort ascription `?[term : type]` over `typeCheck`, and the
   `smtFun!`/`smtPred!`/`smtRel!` shorthands on top of `smt! fun`, none of which exist. Both
   remaining literal-shaped items are **asymmetric across the layers** and need a decision before
   they can be written: the typed layer gets the sort from the index, while sort-erased `mkSymbol`
   takes a `Srt` and a sort ascription has no index to check against.

   Beyond the fixed forms, **28 of the 253 `op%` entries carry a notation** and the rest are
   reachable only through `![…]`. Adding more runs into the collisions listed under "The `smt!`
   DSL" — division has no notation at all for that reason — so that dispatch has to be settled
   first. Every notated operator whose `nary` is not `.never` already has its bracket form
   (`→[]`, `=[]`, `≠[]`, `<[]`, `≤[]`, `≥[]`, `>[]`, `+[]`, `-[]`, `*[]`, `⊻[]`, `∪[]`, `∩[]`,
   `∖[]`, `⊎[]`, `++[]`, `∧[]`, `∨[]`), and unary minus works through `neg`'s prefix notation.
2. **Instantiation patterns** — the `INST_*` annotations a quantifier carries as a third child.
   See "Quantifiers" for where they would go.
3. **Leftovers** — the cvc5 corners never wrapped (pools, oracles, the parser, operator
   reflection, statistics). See [MISSING.md](.notes/MISSING.md).

Two enum wrappers in [Cvc/Basic.lean](Cvc/Basic.lean) are currently unused by anything —
`Option.Category` and `InputLanguage` — since the code that consumed them was the option-info and
parser surface. They are kept because the areas that want them are on the list above.

## Documentation

The manual and the API reference are Lake projects of their own that `require` the library by
path, and four scripts in the root `lakefile.lean` drive them: `lake run buildManual`/`serveManual`
and `lake run buildApiDocs`/`serveApiDocs`. Serving builds first, then serves with `python3 -m
http.server` on port 8000 until interrupted, or on the port given as argument (`lake run
serveApiDocs 8001`) so that both can be served at once.

| | manual | API reference |
|---|---|---|
| project | `CvcManual`, in the repository | `.lake/docbuild`, generated by the script |
| tool | Verso `v4.35.0` | doc-gen4, the tag `lean-toolchain` names |
| toolchain | `v4.35.0`, the library's | the library's, copied from `lean-toolchain` |
| sources | `CvcManual/CvcManual.lean`, `CvcManual/CvcManual/` | none: it documents `Cvc` |
| built with | `lake exe docs` | `lake build Cvc:docs` |
| output | `CvcManual/_out/html-multi` | `.lake/docbuild/.lake/build/doc` |

**The API reference's project is generated, not committed** — `generateApiDocsProject` in the
lakefile, the same thing `leanprover-community/docgen-action` does (that action cannot be used here:
it reads only a `lakefile.toml`, and this one is a `lakefile.lean` for the scripts). It writes a
`lakefile.toml` sharing `.lake/packages` and requiring doc-gen4 at `docGenRev`'s answer — the
toolchain's version tag, `main` for anything else — plus a copy of `lean-toolchain`. When that file
changes, or there is no manifest yet, it runs `lake update doc-gen4`: doc-gen4 alone, which leaves
the shared `cvc5` at the root manifest's revision (verified; Lake pins it from the library's own
manifest). Otherwise it does nothing, so a rebuild costs nothing extra. A toolchain bump therefore
carries doc-gen4 along with no edit. doc-gen4 never deletes the page of a module that is gone, so a
local output keeps stale pages across versions; the Pages workflow excludes the project's build
directory from its cache for that reason.

- **The scripts run each project under its own toolchain**, through `elan run --install
  <lean-toolchain> lake …` with the outer `lake`'s variables cleared (`lakeEnvVars`, the list Verso
  uses for the same purpose). Without that the inner `lake` inherits the root's toolchain.
- **A path dependency builds in the dependency's own `.lake`**, so a sub-project rebuilds the
  library there unless its build traces match the root's — and a separate packages directory, with
  its own cvc5 checkout, is enough to make them differ. So **both documentation projects share the
  root's packages directory**: the generated API project with `packagesDir = "../packages"` (from
  `.lake/docbuild`), the manual with `packagesDir = "../.lake/packages"` in `CvcManual`'s
  `lakefile.toml`. Measured: a manual or API build after a root build rebuilds none of the library,
  and the next root build none either; before the manual shared it, each manual build rebuilt all
  126 library modules and each root build rebuilt them back. Verso and its dependencies therefore
  live in `.lake/packages`. **The cost is that the three projects must agree** on every package
  they share — `cvc5` with the root, `Cli` and `MD4Lean` between doc-gen4 and Verso. They do at
  `v4.35.0`; a toolchain bump that moves one project's revision but not another's has them check
  out different revisions of one directory in turn.
- **The manual links code into the published API reference**, `apiTargets` in
  `CvcManual/Main.lean`, rooted at `apiRoot` (`https://www.anzenlang.io/cvc.lean/api`, upstream's
  site, so a fork's manual links to upstream's reference). A constant goes through doc-gen4's
  `find/?pattern=<name>#doc`, since rendering does not know its module. The links are appended after
  Verso's own, so a constant whose docstring the manual shows links there first and to the API from
  the hover menu. A definition made in a manual example gets no API link.
- **Docstrings need `import all`** — under the module system a docstring travels with a module's
  non-exported data, public declaration or not — and `import all` exposes `Term α`'s definition,
  which erases the typed layer's errors. So a manual page showing docstrings cannot also show sort
  errors: those live in sub-pages with plain imports, `{include}`d (`CvcManual.Terms.*Examples`,
  `CvcManual.Env.SafetyErrors`). Verso's external `anchor`/`anchorError` examples, compiled in a
  separate project, would allow inline error examples instead; nothing uses them yet.
- **Every docstring in the manual is included with `{decl X}`**, `{docstring X}` with a foldable
  body, defined in `CvcManual/CvcManual/Decl.lean` (a page needs `public import CvcManual.Decl` and
  `open CvcManual`). The box keeps Verso's signature line; the docstring, fields or constructors,
  and a definition's **equations** (one per equation theorem `getEqnsFor?` generates, shown as
  `lhs = rhs`) sit in a `<details>` block. Defaults: a type (a definition whose type ends in a
  sort) starts open and shows its equations if its body is exposed; a structure or inductive starts
  folded beyond two fields or constructors; anything else — every function — starts folded, with no
  equations. `+folded`/`-folded` and `+equations`/`-equations` override, but an **unexposed** body
  (`Term`, `Srt`, `Solver.Proof`) is never shown: `+equations` on one is an error. Exposure is read
  through the page's public scope, so a page needs `public import Cvc` (Terms had none, and every
  alias there looked unexposed); `{decl}` errors rather than guess when the name is missing from it.
  It mirrors Verso's `docstring` command and copies its `getExtras`, which Verso does not export,
  so a Verso bump may need the copy refreshed. Equations need `import all` of the declaring module,
  as docstrings do.

## The lean-cvc5 dependency

Vendored at `.lake/packages/cvc5` (~25k lines of Lean). Worth reading when a wrapper misbehaves.

- [`cvc5.lean`](.lake/packages/cvc5/cvc5.lean) (3.6k lines) — the entire API in one file. Types are
  `opaque … : NonemptyType` + `def T : Type := TImpl.type`; methods use `extern_def` (a macro from
  `cvc5/Init.lean` wrapping `@[extern "…"] opaque`).
- `cvc5.Error` = `missingValue | error | recoverable | unsupported | option`.
- `cvc5.EnvT m := ExceptT Error m`, `cvc5.Env := EnvT BaseIO`, `Env.run : Env α → BaseIO (Except
  Error α)`. Note this is a plain `ExceptT` — the term-manager threading is cvc.lean's addition.
- `cvc5.TermManager.new : Env TermManager`; `cvc5.Solver.new : TermManager → Env Solver`.
- Namespaces: `Sort`, `Op`, `Term`, `Proof`, `TermManager` (all `mk*` sort/term constructors),
  `Solver`, `Grammar`, `Command`, `SymbolManager`, `InputParser`, `Result`, `SynthResult`,
  `Datatype*`.
- `cvc5/Kind.lean`, `cvc5/ProofRule.lean`, `cvc5/SkolemId.lean`, `cvc5/Types.lean` are **generated**
  by `PreBuild.lean` from the cvc5 C++ headers during the `cvc5Enums` lake target, which also
  downloads the cvc5 static release for the current platform. Do not hand-edit.
- Its own tests under `cvc5Test/Unit/Api*.lean` are the best reference for what the raw API does.
- Known gaps (from its README): `Term.getStringValue`, statistics, option info, driver options,
  plugins, parser stream input. cvc.lean works around the string one by parsing `term.toString`
  and undoing its SMT-LIB escapes (`""`, `\u{…}`) — see `Untyped.Term.getStringValue` in
  [Cvc/Untyped/Theory/String.lean](Cvc/Untyped/Theory/String.lean). The other direction,
  `mkStringValue`, writes every character outside printable ASCII (and `\`) as `\u{…}`, since cvc5
  refuses them raw; the value conversions and `smt!`'s string literals go through it, so a Lean
  string, Lean's escapes included, is the string the term denotes.
