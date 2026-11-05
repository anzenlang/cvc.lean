# Problems in the cvc5 C++ API

Bugs and sharp edges found in cvc5 itself while building this wrapper. Everything here is at the
**C++ API level** — reproduced against cvc5's own headers and static library, with no Lean and no
[lean-cvc5](https://github.com/abdoo8080/lean-cvc5) involved, so that each entry is something the
cvc5 maintainers can act on directly.

This is not the list of things cvc.lean does not wrap — that is [MISSING.md](MISSING.md) — nor of
things it has decided not to do, which is [TODO.md](TODO.md).

Found against **cvc5 1.3.2** (`git 86cecd8`, macOS arm64 static release, built 2025-12-12), the
build vendored under `.lake/packages/cvc5/cvc5-macOS-arm64-static/`, reached through lean-cvc5
`a3ffc29`.

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
