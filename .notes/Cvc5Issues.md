# Problems in the cvc5 C++ API

Bugs and sharp edges found in cvc5 itself while building this wrapper. Everything here is at the
**C++ API level** — reproduced against cvc5's own headers and static library, with no Lean and no
[lean-cvc5](https://github.com/abdoo8080/lean-cvc5) involved, so that each entry is something the
cvc5 maintainers can act on directly. The exceptions are entries 8, 11 and 12, which concern
lean-cvc5 rather than cvc5's API — the cvc5 build it distributes, its C++ glue, and its docstrings.
Each is written as an issue to file against lean-cvc5.

This is not the list of things cvc.lean does not wrap — that is [MISSING.md](MISSING.md) — nor of
things it has decided not to do, which is [TODO.md](TODO.md).

Found against **cvc5 1.3.2** (`git 86cecd8`, macOS arm64 static release, built 2025-12-12), the
build vendored under `.lake/packages/cvc5/cvc5-macOS-arm64-static/`, reached through lean-cvc5
`a3ffc29`. lean-cvc5's latest revision, `d19a134` (2026-11-02), still downloads that release. The
entries addressed to lean-cvc5 are stated against `d19a134`.

## Reproducing

Entries 1 and 2 share the program below; the later entries carry their own snippets, which
slot into the same skeleton. Compiled and run against the vendored release:

```bash
R=.lake/packages/cvc5/cvc5-macOS-arm64-static
clang++ -std=c++17 -I$R/include repro.cpp -o repro \
  $R/lib/libcvc5.a $R/lib/libcadical.a $R/lib/libpicpoly.a $R/lib/libpicpolyxx.a \
  $R/lib/libgmp.a $R/lib/libgmpxx.a
./repro
```

```cpp
#include <cvc5/cvc5.h>
#include <iostream>
using namespace cvc5;

int main() {
  TermManager tm;
  Solver s(tm);
  s.setOption("produce-proofs", "true");
  Term b = s.declareFun("b", {}, tm.getBooleanSort());
  s.assertFormula(b);
  s.assertFormula(tm.mkTerm(Kind::NOT, {b}));
  std::cout << "check-sat: " << s.checkSat() << std::endl;

  // (1) the header says this is the case getRewriteRule() *requires*
  std::vector<Proof> full = s.getProof();
  std::cout << "root rule: " << full[0].getRule() << std::endl;
  try {
    full[0].getRewriteRule();
    std::cout << "getRewriteRule: returned" << std::endl;
  } catch (const CVC5ApiException& e) {
    std::cout << "getRewriteRule: threw: " << e.what() << std::endl;
  }

  // (2) a non-FULL component printed with a non-NONE format
  std::vector<Proof> sat = s.getProof(modes::ProofComponent::SAT);
  std::cout << "sat component rule: " << sat[0].getRule() << std::endl;
  std::cout << "about to call proofToString with the default format..." << std::endl;
  std::cout.flush();
  try {
    std::string out = s.proofToString(sat[0]);
    std::cout << "proofToString: returned " << out.size() << " chars" << std::endl;
  } catch (const CVC5ApiException& e) {
    std::cout << "proofToString: threw: " << e.what() << std::endl;
  }
  std::cout << "still alive" << std::endl;
  return 0;
}
```

Output:

```
check-sat: unsat
root rule: SCOPE
getRewriteRule: threw: expected `getRule()` to return `DSL_REWRITE` or `THEORY_REWRITE`, got SCOPE instead.
sat component rule: ASSUME
about to call proofToString with the default format...
[exit 139 — SIGSEGV; "still alive" is never reached]
```

## 1. `Proof::getRewriteRule()`'s documented precondition is inverted

**Severity: documentation, but the kind that gets copied.** A caller who follows the doc comment
calls the function in exactly the case that fails.

`cvc5.h:3719-3728` reads:

```cpp
/**
 * Get the proof rewrite rule used  by the root step of the proof.
 *
 * Requires that `getRule()` does not return #DSL_REWRITE or
 * #THEORY_REWRITE.
 *
 * @return The proof rewrite rule.
 *
 */
ProofRewriteRule getRewriteRule() const;
```

The implementation requires the opposite, and says so itself:

```
expected `getRule()` to return `DSL_REWRITE` or `THEORY_REWRITE`, got SCOPE instead.
```

Confirmed by walking a whole proof tree: `getRewriteRule()` succeeds on precisely the steps whose
rule is `DSL_REWRITE` or `THEORY_REWRITE`, and throws on every other rule. Over the refutation of
`x + 0 ≠ x` with `--proof-granularity=dsl-rewrite`, the rules observed were `SCOPE`, `ASSUME`,
`CONG`, `REFL`, `TRANS`, `EVALUATE`, `EQ_RESOLVE`, `ARITH_POLY_NORM`, `DSL_REWRITE` and
`THEORY_REWRITE` — and only the last two answered.

The fix is to drop the word "not". (While that line is being touched: "used  by" has a doubled
space.)

**It propagates.** lean-cvc5 transcribes the header's wording verbatim into `cvc5.lean`, so the
inverted condition reaches downstream bindings, where it is naturally read as a precondition to
encode in a type. That is how it reached this library, where the resulting wrapper could only ever
have been called in the failing case.

## 2. `Solver::proofToString()` crashes the process on a documented misuse

**Severity: high.** A library API kills its host process instead of raising an error the host can
handle.

`cvc5.h:6151-6165` documents the requirement:

```cpp
 * @param format The proof format used to print the proof.  Must be
 * `modes::ProofFormat::NONE` if the proof is from a component other than
 * `modes::ProofComponent::FULL`.
```

Violating it terminates the process with **SIGSEGV** (exit 139). No exception is thrown, nothing is
printed, and there is nothing for the caller to catch. Respecting it works: the same call with
`modes::ProofFormat::NONE` returns normally, so the precondition itself is fine — only its
enforcement is not.

**The inconsistency is the point.** cvc5 already handles this class of mistake properly elsewhere,
including in the very same program: misusing `Proof::getRewriteRule()` raises a `CVC5ApiException`
carrying a message that names the problem. Two documented preconditions on the proof API, violated
the same way, and one is a catchable exception while the other is process death. A `CVC5_API_CHECK`
on `format` against the proof's component would make them consistent.

Reachable only through the C++ API: the `cvc5` binary never makes this call, and
`(get-proof :sat)` on the command line is unaffected whatever `--proof-format-mode` is set to.

## 3. A mismatched `SEP_PTO` is reported as a `set.union` type error

**Severity: usability.** The message names neither the operator at fault nor the heap it conflicts
with, and mentions a `Set` sort the caller never wrote.

`Solver::declareSepHeap(locSort, dataSort)` fixes the heap's sorts, but `SEP_PTO` is built on the
term manager and is checked against **nothing** at construction. Against a heap of `Loc × Int`:

```cpp
s.declareSepHeap(loc, dat);                                     // Loc, Int
Term bad = tm.mkTerm(Kind::SEP_PTO, {tm.mkInteger(1), tm.mkBoolean(true)});
std::cout << bad << " : " << bad.getSort() << std::endl;        // (pto 1 true) : Bool  — accepted
s.assertFormula(bad);
s.checkSat();
```

builds `(pto 1 true)` without complaint, and only at `checkSat()` throws:

```
Operator set.union expects two sets of comparable type. Found types '(Set Loc)' and '(Set Int)'.
```

That is the heap-as-sets encoding leaking. cvc5 knows both the declared heap sorts and the
operands' sorts at construction, so this could be a `CVC5_API_CHECK` on `mkTerm` naming `pto`, the
declared heap and the offending operand.

Compare the two conditions cvc5 *does* report well, in the same area: declaring the heap twice
gives "cannot declare heap types for separation logic more than once. We are declaring heap of type
Int -> Loc, but we already have Loc -> Int", and asserting a separation-logic constraint with no
heap declared names the constraint. Only the sort mismatch is opaque.

**What it costs a wrapper.** cvc.lean checks it instead: `declareSepHeap` answers a handle carrying
the two sorts, `pto` comes off the handle, and the message names the operand and both sorts. Typed,
the handle carries the two Lean types and the mismatch does not typecheck. See the "Separation
logic" section of [CLAUDE.md](../CLAUDE.md).

## 5. `mkRecordSort` accepts duplicate field names

**Severity: usability.** The result is a sort whose fields cannot all be reached.

```cpp
Sort r = tm.mkRecordSort({{"a", tm.getIntegerSort()}, {"a", tm.getBooleanSort()}});
std::cout << r << "\n";                       // __cvc5_record_a_Int_a_Bool
Datatype d = r.getDatatype();
for (size_t s = 0; s < d[0].getNumSelectors(); ++s)
  std::cout << "  " << d[0][s].getName() << " : " << d[0][s].getCodomainSort() << "\n";
```

builds without complaint, giving one constructor with **two selectors both named `a`**, of sorts
`Int` and `Bool`. `Datatype::getSelector("a")` then has two candidates, and a record with two fields
of one name has no meaning to begin with. A `CVC5_API_CHECK` on the field names would refuse it at
construction, where the caller can still act on it.

For contrast, cvc5 does check the fields it cares about: a field of a non-first-class sort is
refused with *"cannot use fields in datatypes that are not first class types"*. Only the names go
unchecked.

**What it costs a wrapper.** cvc.lean checks the names itself in `Srt.record`, so both it and
`Typ.toSrt` refuse the sort — see the "Records" section of [CLAUDE.md](../CLAUDE.md).

## 4. `getValueSepHeap` and `getValueSepNil` do not return what their docs say

**Severity: documentation.**

`cvc5.h:6357-6373` documents them as "obtain the term for the heap" / "@return The term for the
heap", and likewise "the term for nil". Both in fact return a **Bool-sorted formula** characterizing
the model, not a heap value and not a location. On a model of `(pto x v)` over a `Loc × Int` heap:

```
getValueSepHeap : (pto (as @Loc_1 Loc) 0)          : Bool
getValueSepNil  : (= (as sep.nil Loc) (as @Loc_0 Loc)) : Bool
```

Reading the docs, a caller expects the second to be a `Loc` and writes code that takes it for one.
Saying "a formula describing the heap in the current model" would settle it.

**What it costs a wrapper.** A binding cannot defend against it by catching — there is nothing to
catch — so the pairing has to be established before the call. cvc5 makes that awkward by leaving
the component off `Proof`: a proof does not know where it came from, so `proofToString` cannot
check its own precondition even in principle, and neither can a caller holding only the proof.
Carrying the component would let cvc5 turn this into the `CVC5_API_CHECK` it should have been.

cvc.lean works around it by carrying the component *itself*: `Solver.Proof s pc` is indexed by the
`ProofComponent` it was obtained with, `getUnsatProof` propagates it, `getChildren` preserves it,
and the formatted printer takes `fmt = .no ∨ pc = .full` as a proof obligation that `grind`
discharges whenever both are literals. The crashing call therefore does not compile. See the
"Proofs" section of [CLAUDE.md](../CLAUDE.md).

That is a workaround, not a fix, and it costs an index on a type that would otherwise need none.
It also means the violation cannot be *tested* — a test would take the build down rather than fail
— so what the proof suites pin is the obligation instead.

## 6. Asserting a `WITNESS` term aborts the process

**Severity: crash.** A term the API builds without complaint takes the process down when asserted.

```cpp
Sort intSort = tm.getIntegerSort();
Term y = s.declareFun("y", {}, intSort);
Term x = tm.mkVar(intSort, "x");
Term w = tm.mkTerm(Kind::WITNESS,
  {tm.mkTerm(Kind::VARIABLE_LIST, {x}), tm.mkTerm(Kind::GT, {x, y})});
std::cout << "built: " << w << " : " << w.getSort() << std::endl;
s.assertFormula(tm.mkTerm(Kind::GT, {w, tm.mkInteger(5)}));
std::cout << "check-sat: " << s.checkSat() << std::endl;   // inside a try/catch
std::cout << "still alive" << std::endl;
```

Output:

```
built: (witness ((x Int)) (> x y)) : Int
check-sat: Fatal failure within Node cvc5::internal::RemoveTermFormulas::runCurrentInternal(…)
  at src/smt/term_formula_removal.cpp:273
Check failure

 node.getKind()!=Kind::WITNESS
WITNESS should never appear in asserted terms
[exit 134 — SIGABRT; "still alive" is never reached]
```

The internal assertion says the restriction is deliberate, which is fine, but it is enforced by an
abort deep inside `checkSat` instead of a `CVC5_API_CHECK` at `mkTerm` or `assertFormula`, so the
`try`/`catch` around the call cannot help. Either refusing `WITNESS` in `mkTerm` when it is not
meant for users, or checking asserted formulas for it, would turn this into an exception.

**What it costs a wrapper.** cvc.lean does not wrap `WITNESS` at all; its quantifier module says
why.

## 7. Grammars and declared constants are made through a solver but belong to the term manager

**Severity: API design.** Two things the API offers only on `Solver` have nothing to do with the
solver that made them. Nothing breaks; the shape of the API suggests a scoping that does not exist.

```cpp
TermManager tm;
Sort i = tm.getIntegerSort();
Solver s1(tm), s2(tm);
s2.setOption("produce-interpolants", "true");
s1.setOption("produce-models", "true");
s2.setOption("produce-models", "true");

// (a) a grammar can only be made by a solver, yet any solver of the term manager takes it
Term a = tm.mkConst(i, "a"), c = tm.mkConst(i, "c");
Term start = tm.mkVar(tm.getBooleanSort(), "start");
Grammar g = s1.mkGrammar({}, {start});            // the only public way to make one
g.addRule(start, tm.mkTerm(Kind::LT, {a, c}));
g.addRule(start, tm.mkTerm(Kind::EQUAL, {a, c}));
s2.assertFormula(tm.mkTerm(Kind::LT, {a, c}));
Term goal = tm.mkTerm(Kind::LT, {a, tm.mkTerm(Kind::ADD, {c, tm.mkInteger(1)})});
std::cout << "s2, interpolant with s1's grammar: " << s2.getInterpolant(goal, g) << std::endl;

// (b) a constant "declared in" s1 is a term-manager constant like any other
Term x = s1.declareFun("x", {}, i);
s2.assertFormula(tm.mkTerm(Kind::EQUAL, {x, tm.mkInteger(7)}));
std::cout << "s2, value of s1's x: " << (s2.checkSat(), s2.getValue(x)) << std::endl;
std::cout << "s1, value of its x : " << (s1.checkSat(), s1.getValue(x)) << std::endl;
std::cout << "s1 x == mkConst x  : " << (x == tm.mkConst(i, "x")) << std::endl;
// and the non-fresh cache is the term manager's, not the declaring solver's
Term y1 = s1.declareFun("y", {}, i, false), y2 = s2.declareFun("y", {}, i, false);
std::cout << "s1 y == s2 y (fresh = false): " << (y1 == y2) << std::endl;
```

Output:

```
s2, interpolant with s1's grammar: (< a c)
s2, value of s1's x: 7
s1, value of its x : 0
s1 x == mkConst x  : 0
s1 y == s2 y (fresh = false): 1
```

**Grammars.** `Solver::mkGrammar` is the only public way to make a `Grammar`: the class's real
constructor is private, `Solver` is its friend, and the public default constructor makes the null
grammar. Yet that private constructor takes a `TermManager*` and no solver, and a grammar built by
`s1` is accepted by `s2` — for interpolation above, and for `synthFun`/`checkSynth` equally. What is
rejected is a grammar from another *term manager* ("Given grammar is not associated with the term
manager of this solver"). Even the freeze after `synthFun` belongs to the grammar object, not to a
solver: once any solver has used it, no other can add a rule. So a grammar is a term-manager object
that can only be made by going through a solver, any solver.

**Declared constants.** `Solver::declareFun` with no parameters makes a `CONSTANT` exactly as
`TermManager::mkConst` does — a fresh one per call, distinct from a same-named constant made the
other way — and the solver that declared it plays no further part: `s2` constrains and evaluates
`s1`'s `x`, `s1` knows nothing of `s2`'s assertion, and each answers its own value. Even the
`fresh = false` cache, the one thing `declareFun` adds over `mkConst`, is the term manager's: `s1`
and `s2` get the *same* `y`. That is faithful to SMT-LIB, where `declare-fun` is a command of the
one solver a script talks to, so the question of which solver owns a symbol never arises. Through an
API holding several solvers over one term manager it does arise, and the method's home answers it
wrongly: `s1.declareFun("x", …)` reads as "a constant local to `s1`", which it is not.

The direction cvc5 has already taken settles which way this should go: `Solver::mkConst` is
deprecated in favor of `TermManager::mkConst`. `mkGrammar` and the declaration methods read as the
part of that migration left behind. A `TermManager::mkGrammar` — the private constructor already
takes exactly what it needs — and either the same treatment for `declareFun` or a documented note
that it is term-manager-level, `fresh = false` cache included, would align the API with what the
objects are.

**What it costs a wrapper.** cvc.lean briefly indexed its grammar types by the solver that built
them, reading the shape of the API as a scoping rule, and removed the index once the test above
showed it forbade something that works. Its grammars are now scope-level, as terms are, built with
`s.mkGrammar` because nothing else exists — any solver of the scope will do. For constants,
`Term.mkSymbol` is the term-manager path and is what cvc.lean's documentation uses.
`Solver.declareConst` still exists, but it carries exactly the illusion described above, and
cvc.lean is considering removing it outright: a symbol is an `Env`-level thing, and a solver-level
spelling of it is worse user experience than having none.

## 8. lean-cvc5's Linux cvc5 needs glibc 2.38, so no executable links

**Severity: high, on Linux.** No executable importing `cvc5` links, whatever it does. Addressed to
[lean-cvc5](https://github.com/abdoo8080/lean-cvc5) rather than cvc5, and written to be filed there
as is.

**Title:** Linux: executables fail to link against the cvc5 release (`undefined symbol:
__isoc23_strtol`)

### Summary

On Linux, any `lean_exe` that imports `cvc5` fails to link, because the downloaded cvc5 static
libraries reference two glibc 2.38 symbols that the glibc Lean links executables against does not
have. Libraries, and so tests run as a `lean_lib`, are unaffected on a recent distribution, which is
presumably why lean-cvc5's own test suite, a library, has never shown it.

### Reproduction

`lean-toolchain`:

```
leanprover/lean4:v4.35.0
```

`lakefile.toml`:

```toml
name = "repro"
defaultTargets = ["repro"]

[[require]]
name = "cvc5"
git = "https://github.com/abdoo8080/lean-cvc5"
rev = "d19a134c237ec7f0cb86c2027062eedeb577a9a9"

[[lean_exe]]
name = "repro"
root = "Main"
```

`Main.lean`:

```lean
import cvc5

def main : IO Unit := do
  match ← cvc5.TermManager.new.run with
  | .ok _ => IO.println "ok"
  | .error _ => IO.println "error"
```

`lake build` on Linux x86_64 then fails at the link:

```
ld.lld: error: undefined symbol: __isoc23_strtol
>>> referenced by SimpSolver.cc
>>>               SimpSolver.cc.o:(cvc5::internal::Minisat::IntOption::parse(char const*)) in archive …/.lake/packages/cvc5/cvc5-Linux-x86_64-static/lib/libcvc5.a

ld.lld: error: undefined symbol: __isoc23_fscanf
>>> referenced by resources.cpp
>>>               resources.o:(CaDiCaL::current_resident_set_size()) in archive …/.lake/packages/cvc5/cvc5-Linux-x86_64-static/lib/libcadical.a
clang: error: linker command failed with exit code 1 (use -v to see invocation)
```

That output is from GitHub Actions' `ubuntu-latest`, linking an executable of a project that
depends on lean-cvc5 `41e4779` through cvc.lean, on Lean v4.35.0. `d19a134` differs from `41e4779`
only in its Lean version: it downloads the same cvc5 release and links it the same way. The minimal
project above was not run as such; its `Main.lean` typechecks against that `cvc5.lean`, and the link
it ends with is the same.

### Cause

The `cvc5-1.3.2` release lean-cvc5 downloads from `abdoo8080/cvc5` was compiled on Ubuntu 24.04,
whose glibc is 2.39: its objects carry `GCC: (Ubuntu 14.2.0-4ubuntu2~24.04) 14.2.0`. From glibc
2.38, compiling with `_GNU_SOURCE`, which g++ always defines, or with `-std=c2x` redirects `strtol`,
`scanf` and their relatives to the C23 variants `__isoc23_*`. Lean's toolchain links executables
against the glibc it bundles, which predates 2.38, so the variants are not there.

Shared libraries link anyway, leaving the symbols to the system's glibc when they are loaded, which
is why building a library works on a recent distribution. On one whose glibc is older than 2.38
(Ubuntu 22.04, Debian 12, RHEL 9), the symbols are missing at load time too, so loading the
precompiled modules presumably fails there as well. That part has not been verified.

`nm -u` over every archive of both Linux releases finds exactly these references, the same on x86_64
and arm64:

| archive | object | symbol |
|---|---|---|
| `libcvc5.a` | `Solver.cc.o`, `SimpSolver.cc.o` (MiniSat) | `__isoc23_strtol` |
| `libgmp.a` | `doscan.o` | `__isoc23_strtol` |
| `libcadical.a` | `resources.o` | `__isoc23_fscanf` |

No other `__isoc23_*` symbol is referenced, nor `arc4random`, `strlcpy` or `strlcat`, the other
functions recent glibc releases added.

### Suggested fix

- **Build the Linux release against a glibc older than 2.38**: on the `ubuntu-22.04` runner (glibc
  2.35), or in a `manylinux_2_28` container (glibc 2.28) for the widest reach. A library built
  against an old glibc runs against any newer one.
- **Until then, ship the two symbols.** Adding the forwarding definitions below to lean-cvc5's
  `libs` would fix every downstream project at once. lean-cvc5's `moreLinkObjs` also go into its
  shared library, so this would cover loading on an old glibc as well, which a downstream project
  cannot reach.
- **Link an executable in CI.** A `lean_exe` among lean-cvc5's tests would catch a regression. The
  test driver being a `lean_lib`, nothing there links an executable today.

### Workaround

cvc.lean links this into its library with `moreLinkObjs`, compiled with the C compiler Lean ships
(Lake's `buildLeanO`) so that a user needs no C compiler of their own:

```c
#if defined(__linux__)
#include <stdarg.h>

typedef struct _IO_FILE FILE;

long strtol(const char *nptr, char **endptr, int base);
int __isoc99_vfscanf(FILE *stream, const char *format, va_list args);

long __isoc23_strtol(const char *nptr, char **endptr, int base) {
  return strtol(nptr, endptr, base);
}

int __isoc23_fscanf(FILE *stream, const char *format, ...) {
  va_list args;
  va_start(args, format);
  int result = __isoc99_vfscanf(stream, format, args);
  va_end(args);
  return result;
}
#endif
```

It includes no libc header, declaring what it calls itself, for two reasons. Lean's toolchain
ships the compiler's own headers, `stdarg.h` among them, but no libc's, so `stdio.h` is not found.
And glibc's headers from 2.38 on, under `_GNU_SOURCE` or C23, would redirect the forwarding calls
to the very functions being defined. `__isoc99_vfscanf` is the symbol glibc's headers give
`vfscanf` in C99 and later.

The C23 variants differ from the C99 ones only in reading `0b` binary literals (`strtol` with base
0 or 2, `fscanf`'s `%i`), which the callers have no use for: MiniSat's integer options, GMP's
`scanf`, and CaDiCaL reading its resident set size from `/proc`.

**What it costs a wrapper.** cvc.lean carries the shim in `Cvc/glibc_compat.c`, with a target in the
root lakefile, both marked temporary, to be removed once this is fixed. It covers executables only.
Lake keeps a library's `moreLinkObjs` out of the per-module shared libraries its own build loads,
and lean-cvc5's shared library, the one referencing the symbols, is loaded before cvc.lean's
anyway. So an old-glibc host is left as it was.

## 9. `getProof()` aborts the process under `proof-mode sat-proof` with unsat cores

**Severity: crash.** Two options, both accepted by `setOption`, then the default `getProof()` takes
the process down.

```cpp
s.setOption("produce-unsat-cores", "true");
s.setOption("proof-mode", "sat-proof");
Sort bool_ = tm.getBooleanSort();
Term a = s.declareFun("a", {}, bool_), b = s.declareFun("b", {}, bool_),
     c = s.declareFun("c", {}, bool_), d = s.declareFun("d", {}, bool_);
s.assertFormula(tm.mkTerm(Kind::OR, {tm.mkTerm(Kind::AND, {a, b}), tm.mkTerm(Kind::AND, {c, d})}));
s.assertFormula(tm.mkTerm(Kind::OR, {tm.mkTerm(Kind::NOT, {a}), tm.mkTerm(Kind::NOT, {b})}));
s.assertFormula(tm.mkTerm(Kind::OR, {tm.mkTerm(Kind::NOT, {c}), tm.mkTerm(Kind::NOT, {d})}));
std::cout << "check-sat: " << s.checkSat() << std::endl;
std::cout << "unsat-cores-mode: " << s.getOption("unsat-cores-mode") << std::endl;
std::vector<Proof> sat = s.getProof(modes::ProofComponent::SAT);
std::cout << "sat component: " << sat[0].getRule() << " ⊢ " << sat[0].getResult() << std::endl;
std::cout << "full proof..." << std::endl;
std::vector<Proof> full = s.getProof();   // inside a try/catch
std::cout << "still alive" << std::endl;
```

Output:

```
check-sat: unsat
unsat-cores-mode: assumptions
sat component: ASSUME ⊢ false
full proof...
Fatal failure within std::shared_ptr<ProofNode> cvc5::internal::ProofNodeManager::mkScope(…)
  at src/proof/proof_node_manager.cpp:248
Unreachable code reached Generated a proof that is not closed by the scope:
Free assumption: false
- assumption: (or (not a) (not b))
- assumption: (or (not c) (not d))
- assumption: (or (and a b) (and c d))
Use -t dump-proof-error for details on proof
[exit 134 — SIGABRT; "still alive" is never reached]
```

**What happens.** `produce-unsat-cores` selects `unsat-cores-mode assumptions`, in which the SAT
solver finds its core through assumptions and records no refutation. `proof-mode sat-proof` turns
`produce-proofs` on regardless, so proofs are built, and the SAT component comes out as a bare
`ASSUME false`: an open assumption, not a proof of anything. The full proof wraps it in a `SCOPE`
over the assertions, and the check that the scope leaves nothing open is an `Unreachable` abort
rather than an exception.

Setting `produce-proofs true` explicitly, before or after the other options, avoids it: cvc5 then
switches `unsat-cores-mode` to `sat-proof` itself. `proof-mode sat-proof` turns proofs on without
that switch. On the same problem:

| options | `getProof(SAT)` | `getProof()` |
|---|---|---|
| `produce-unsat-cores true`, `proof-mode sat-proof` | `ASSUME ⊢ false` | abort |
| `unsat-cores-mode assumptions`, `proof-mode sat-proof` | `ASSUME ⊢ false` | abort |
| the first row, then `produce-proofs true` | `CHAIN_M_RESOLUTION ⊢ false` | a proof |
| `produce-unsat-cores true`, `unsat-cores-mode sat-proof`, `proof-mode sat-proof` | `CHAIN_M_RESOLUTION ⊢ false` | a proof |
| `produce-unsat-cores true` alone (`proof-mode` reported as `pp-only`) | exception, below | a proof, refuted by `TRUST` (entry 10) |

The exception in the last row is the right answer, and what `sat-proof` should give as well:
"Cannot get a proof for this component when SAT solver is not proof producing." Either that, or
refusing `proof-mode sat-proof` together with assumption-based cores, or switching the cores mode as
an explicit `produce-proofs` does, would turn the abort into something a caller can handle.

**What it costs a wrapper.** Options pass through `setOption` as strings, so cvc.lean cannot rule
the combination out, and a library user who sets these two options loses the process. Nothing in the
library sets them.

## 10. Three documented proof rules that cvc5 never seems to produce

**Severity: documentation, or dead code.** `cvc5_proof_rule.h` documents `SAT_REFUTATION`, `SPLIT`
and `PAIRWISE_CONG`, and a wrapper decoding proof steps has to handle all three. We could not get
cvc5 to produce any of them, so a decoder written from the documentation alone cannot be tested.
Is each of them still produced, and if so, by which problem and options?

The program below prints the rules of the full proof, with how many distinct steps use each, for the
two problems that should come closest to producing the first and the third:

```cpp
// every rule in the proof, with its number of distinct steps
std::map<std::string, int> rules(const Proof& root) {
  std::map<std::string, int> out;
  std::vector<Proof> todo{root}, seen;
  while (!todo.empty()) {
    Proof p = todo.back(); todo.pop_back();
    bool dup = false;
    for (auto& q : seen) if (q == p) { dup = true; break; }
    if (dup) continue;
    seen.push_back(p);
    std::string r = toString(p.getRule());
    if (p.getRule() == ProofRule::TRUST) {
      r += "(" + p.getArguments()[0].toString() + ")";
      std::cout << "  TRUST " << p.getArguments()[0] << ", " << p.getChildren().size()
                << " premises: ";
      for (auto& c : p.getChildren()) std::cout << c.getResult() << "; ";
      std::cout << "⊢ " << p.getResult() << std::endl;
    }
    out[r]++;
    for (auto& c : p.getChildren()) todo.push_back(c);
  }
  return out;
}

void run(const std::string& name, std::vector<std::pair<std::string, std::string>> opts,
         std::function<void(TermManager&, Solver&)> setup) {
  TermManager tm;
  Solver s(tm);
  for (auto& [k, v] : opts) s.setOption(k, v);
  setup(tm, s);
  std::cout << name << ": " << s.checkSat() << "\n ";
  for (auto& [r, n] : rules(s.getProof()[0])) std::cout << " " << r << "×" << n;
  std::cout << std::endl;
}

int main() {
  // the problem of entry 9
  auto clauses = [](TermManager& tm, Solver& s) { /* … */ };
  // SAT_REFUTATION: "SAT Refutation for assumption-based unsat cores"
  run("proofs", {{"produce-proofs", "true"}}, clauses);
  run("assumption cores", {{"produce-unsat-cores", "true"}}, clauses);
  run("sat-external-prove",
      {{"produce-proofs", "true"}, {"prop-proof-mode", "sat-external-prove"}}, clauses);

  // PAIRWISE_CONG: "used only for congruence of terms whose kind is DISTINCT"
  auto distinct = [](TermManager& tm, Solver& s) {
    Sort is = tm.getIntegerSort();
    Term x = s.declareFun("x", {}, is), y = s.declareFun("y", {}, is),
         z = s.declareFun("z", {}, is);
    // (distinct (+ x 0) x y z): rewriting (+ x 0) to x under DISTINCT needs congruence over it
    s.assertFormula(tm.mkTerm(Kind::DISTINCT,
        {tm.mkTerm(Kind::ADD, {x, tm.mkInteger(0)}), x, y, z}));
  };
  for (auto g : {"macro", "dsl-rewrite", "theory-rewrite"})
    run(std::string("distinct, ") + g,
        {{"produce-proofs", "true"}, {"proof-granularity", g}}, distinct);
  return 0;
}
```

Output:

```
proofs: unsat
  ASSUME×3 CHAIN_M_RESOLUTION×5 CNF_AND_POS×4 REORDERING×4 SCOPE×2
assumption cores: unsat
   TRUST 3, 3 premises: (or (and a b) (and c d)); (or (not a) (not b)); (or (not c) (not d)); ⊢ false
 ASSUME×3 SCOPE×2 TRUST(3)×1
sat-external-prove: unsat
  ASSUME×3 CHAIN_M_RESOLUTION×5 CNF_AND_POS×4 REORDERING×4 SCOPE×2
distinct, macro: unsat
  ASSUME×1 EQ_RESOLVE×1 MACRO_SR_EQ_INTRO×1 SCOPE×2
distinct, dsl-rewrite: unsat
  ABSORB×1 ARITH_POLY_NORM×1 ASSUME×1 CONG×6 DSL_REWRITE×1 EQ_RESOLVE×1 EVALUATE×1 NARY_CONG×1 REFL×6 SCOPE×2 THEORY_REWRITE×1 TRANS×4
distinct, theory-rewrite: unsat
  ASSUME×1 CONG×6 EQ_RESOLVE×1 NARY_CONG×1 REFL×6 SCOPE×2 TRANS×4 TRUST_THEORY_REWRITE×5
```

- **`SAT_REFUTATION`** is documented as the "SAT Refutation for assumption-based unsat cores", with
  the core as premises and `false` as conclusion. In exactly that mode — `produce-unsat-cores`,
  which selects `unsat-cores-mode assumptions` — the refutation is a `TRUST` step of trust id 3
  instead, with that very shape: the three assertions as premises, `false` as conclusion. Under
  `proof-mode sat-proof` the step is missing altogether and the process aborts (entry 9). Asking for
  the `SAT` or `PREPROCESS` component, or checking with assumptions, changes nothing. Should this
  `TRUST` step be a `SAT_REFUTATION`, or is the rule's documentation out of date?
  `prop-proof-mode sat-external-prove` is accepted and silently ignored with the default SAT solver,
  so `SAT_EXTERNAL_PROVE` does not appear either, and `sat-solver cadical` is refused with proofs:
  "CaDiCaL not supported with proofs or unsat cores".
- **`PAIRWISE_CONG`** is documented as "used only for congruence of terms whose kind is
  `DISTINCT`". At every granularity, `DISTINCT` is rewritten into its pairwise disequalities before
  its arguments are, so the congruence is over the expansion — `CONG` and `NARY_CONG` above —
  never over the `DISTINCT` itself. The same holds with 3, 4 and 12 arguments, and when a
  substitution applies under the `DISTINCT`.
- **`SPLIT`**, `F ∨ ¬F` from nothing, never appeared on any of the problems that need a case split.
  Arithmetic branch and bound concludes with `ARITH_TRICHOTOMY` instead, with `arith-brab` on or
  off, and datatypes split with `DT_SPLIT`. A UF and linear arithmetic pigeonhole needing theory
  combination, the non-linear split on zero, string length splits, quantifier instantiation and
  counterexample-guided instantiation, sets, arrays, and Boolean structure meant for the circuit
  propagator did not produce it either.

**What it costs a wrapper.** cvc.lean decodes each of the three into a constructor of its own, from
the documented layout alone. These are the only decoded rules its tests cannot show decoded on a
real proof, so a layout change would go unnoticed for them, where for every other rule a test would
fail.

## 11. lean-cvc5's `mkAbstractSort` reads its kind at the wrong width, so it fails on Windows

**Severity: medium, on Windows.** `TermManager.mkAbstractSort` fails there for whichever kind,
unless the call happens to work. Addressed to [lean-cvc5](https://github.com/abdoo8080/lean-cvc5)
rather than cvc5, and written to be filed there as is.

**Title:** Windows: `mkAbstractSort` fails with "cannot construct abstract type for kind
UNDEFINED_SORT_KIND"

### Summary

`termManager_mkAbstractSort` in `ffi/ffi.cpp` takes its kind as a `uint16_t`, but `SortKind` has
23 constructors, so Lean passes it as a `uint8_t`: the C Lean generates for the `extern` declares

```c
lean_object* termManager_mkAbstractSort(lean_object*, uint8_t);
```

against the definition

```cpp
LEAN_EXPORT lean_obj_res termManager_mkAbstractSort(lean_obj_arg tm,
                                                    uint16_t kind)
{
  CVC5_LEAN_API_TRY_CATCH_ENV_BEGIN;
  SortKind k = static_cast<SortKind>(static_cast<int32_t>(kind) - 2);
```

So the function reads a byte the caller never set. On Linux and macOS that byte is zero in
practice and the call works; on Windows it is not, and cvc5 refuses the kind.

### Reproduction

The `lean-toolchain` and `lakefile.toml` of entry 8, with this `Main.lean`:

```lean
import cvc5

def main : IO Unit := do
  let res ← (do
    let tm ← cvc5.TermManager.new
    let s ← tm.mkAbstractSort .BITVECTOR_SORT
    return s.toString : cvc5.Env String).run
  match res with
  | .ok s => IO.println s!"ok: {s}"
  | .error e => IO.println s!"error: {e}"
```

Run on macOS arm64, as `#eval main`, it prints `ok: ?BITVECTOR_TYPE`. On GitHub Actions'
`windows-latest` (MSYS2's CLANG64, Lean v4.35.0), the same call for `BITVECTOR_SORT`, made by
cvc.lean's tests through lean-cvc5 `41e4779`, whose `ffi/ffi.cpp` is `d19a134`'s, failed with

```
cannot construct abstract type for kind UNDEFINED_SORT_KIND
```

while `ABSTRACT_SORT`, earlier in the same run, succeeded. The minimal project above was not run on
Windows as such.

What cvc5 does with a stray high byte is shown on any platform by the C++ below, slotted into the
skeleton of "Reproducing": it computes the kind as `termManager_mkAbstractSort` does from the 16
bits it reads.

```cpp
static void attempt(TermManager& tm, uint16_t received) {
  SortKind k = static_cast<SortKind>(static_cast<int32_t>(received) - 2);
  std::cout << "received " << received << " -> kind " << k << ": ";
  try {
    std::cout << tm.mkAbstractSort(k) << std::endl;
  } catch (const CVC5ApiException& e) {
    std::cout << "threw: " << e.what() << std::endl;
  }
}

int main() {
  TermManager tm;
  uint8_t bv = static_cast<uint8_t>(static_cast<int32_t>(SortKind::BITVECTOR_SORT) + 2);
  attempt(tm, bv);           // the byte Lean passes, high byte clear
  attempt(tm, 0x0100 | bv);  // the same byte with a stray high byte
  attempt(tm, 0xab00 | bv);
  return 0;
}
```

```
received 7 -> kind BITVECTOR_SORT: ?BITVECTOR_TYPE
received 263 -> kind UNDEFINED_SORT_KIND: threw: cannot construct abstract type for kind UNDEFINED_SORT_KIND
received 43783 -> kind UNDEFINED_SORT_KIND: threw: cannot construct abstract type for kind UNDEFINED_SORT_KIND
```

cvc5 prints any value outside `SortKind` as `UNDEFINED_SORT_KIND`, which is the Windows message.

### Cause

A `uint8_t` argument travels in the low byte of a register, and the calling conventions leave the
rest unspecified, with one exception: Apple's arm64 ABI makes the caller extend it to 32 bits.
Compilers targeting Linux and macOS x86_64 extend it too, by convention rather than requirement,
which is why the read has worked there. The Windows x64 convention gives no such guarantee, so the
high byte `termManager_mkAbstractSort` reads is whatever the register held.

A non-zero high byte makes the kind at least 254, beyond every `SortKind`, so the failure is always
cvc5 refusing the kind, never another valid kind silently built. When the byte happens to be zero
the call succeeds, which is why `ABSTRACT_SORT` passed. lean-cvc5's own tests call `mkAbstractSort`
with `BITVECTOR_SORT` and run on Windows in its CI, so whether they pass there depends on what that
register holds at that call. Linux arm64 relies on the same convention as Linux x86_64 and has not
been seen to fail.

Every other exported function taking an enum agrees with Lean on the width: `Kind` (297
constructors) and `ProofRewriteRule` (527) are `uint16_t` on both sides, and every enum of fewer
than 256 constructors is read as a `uint8_t`.

### Suggested fix

Declare the parameter `uint8_t kind` in `termManager_mkAbstractSort`.

Unrelated to Windows but next to it: `sortKind_hash` casts its argument without the `- 2` that
`sortKind_toString` and `termManager_mkAbstractSort` subtract. The hash stays consistent, the shift
being the same for every value, but it hashes a different `SortKind` from the one meant.

### Workaround

None. cvc5's API has no other way to build an abstract sort, and patching `ffi.cpp` downstream
would mean carrying a fork of lean-cvc5.

**What it costs a wrapper.** On Windows, cvc.lean's `Srt.any`, `Srt.abstract`, and building the sort
of an abstract `Typ?` each fail with that error, or work, depending on the call. Its `CvcTests.Srt`
fails there for that reason, which is what keeps Windows out of cvc.lean's CI.


## 12. lean-cvc5 docstrings that describe another declaration, or are not Markdown

**Severity: low.** Documentation only, but a library inheriting these docstrings
(`@[inherit_doc cvc5.…]`) passes the mistakes on to its own users. Addressed to
[lean-cvc5](https://github.com/abdoo8080/lean-cvc5) and written to be filed there as is.

**Title:** Docstring fixes: copy-paste slips, typos, leftover reStructuredText

### Summary

At lean-cvc5 `d19a134`, in `cvc5.lean` unless noted:

- `Term.isStringValue` carries `getIntegerValue`'s docstring: "Get the native integral value of an
  integral value." It should read "Determine if this term is a string value."
- `Solver.getUnsatAssumptions` says "Requires to enable option `produce-unsat-assumption`"; the
  option is `produce-unsat-assumptions`.
- `Sort.hasSymbol` is `Term.hasSymbol`'s docstring: "Determine if this term has a symbol (a name).
  For example, free constants and variables have symbols."
- `Sort.getSymbol` says "consrtucting", and names `Solver.mkUninterpretedSort`,
  `Solver.mkUnresolvedSort` and `Solver.mkUninterpretedSortConstructorSort`, which are
  `TermManager` functions.
- `Sort.getArrayIndexSort` and `Sort.getArrayElementSort`: "The array index sort of an array index",
  "The array element sort of an array index", for "of an array sort".
- `DatatypeSelector.toString`: "Gte the string representation of this datatype selector."
- `DatatypeConstructor.toString`: "A string representation of this datatype", for this constructor.
- `DatatypeConstructorDecl.hash`: "Hash function for datatype declarations", for constructor
  declarations.
- `Datatype.isWellFounded`: "thre are no values".
- `Proof.getRule`: "the proof rule used by the root step of the root", for "of the proof".
- `InputLanguage`, in the generated `cvc5/Types.lean`: "The different reasons for returning an
  "unknown" result", which is `UnknownExplanation`'s docstring. The file is generated from cvc5's
  headers by `PreBuild.lean`, so the slip is either there or in the header.
- `Solver.declareFun`, `getUnsatCore`, `getValue` and `getValues` still hold cvc5's reStructuredText
  (`\verbatim embed:rst:leading-asterisk`, `.. code:: smtlib`, `\endverbatim`), which renders as
  text; the other docstrings write the same SMT-LIB snippet as a ```` ```smtlib ```` fence.

### Suggested fix

Correct the wording as indicated above, and replace each `\verbatim` block with a
```` ```smtlib ```` fence.

**What it costs a wrapper.** cvc.lean gives these declarations docstrings of its own rather than
inheriting lean-cvc5's.
