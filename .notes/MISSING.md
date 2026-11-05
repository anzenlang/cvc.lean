# What cvc.lean does not wrap yet

Gaps against [lean-cvc5](../.lake/packages/cvc5/cvc5.lean), by area. This tracks the **API surface**;
`CLAUDE.md`'s "What is left" section tracks this library's own design work, which is a different
list.

Last refreshed against the tree at the same time as the counts below; regenerate them with the two
scripts at the end.

## Summary

| area | size | blocked on |
|---|---|---|
| [Instantiation patterns](#instantiation-patterns) | 6 kinds | — |
| [Parser](#parser) | ~15 functions | — |
| [Tuple projection](#tuple-projection) | the `α × β` index only | a type-level component select |
| [Operator reflection](#operator-reflection) | 5 functions | — |
| [Uninterpreted-sort values](#uninterpreted-sort-values) | 1 kind + 2 functions | — |
| [Cardinality constraints](#cardinality-constraints) | 1 kind + 2 functions | — |
| [Pools and oracles](#pools-and-oracles) | 2 functions | — |
| [Odds and ends](#odds-and-ends) | 5 functions + 1 kind | — |
| [Statistics](#not-bound-by-lean-cvc5-either) | — | lean-cvc5 does not bind it |

Coverage as measured: **282 of 297 term kinds** referenced (`WITNESS` only by the comment
explaining its exclusion), and by namespace —
`Sort` 65/65, `TermManager` 66/72, `Term` 60/76, `Solver` 63/72, every `Datatype*` type complete,
`Grammar` 4/4, `Proof` 5/5, `Result` 4/4, `SynthResult` 3/3, `Op` 4/4, `InputParser` 2/11,
`SymbolManager` 3/6, `Command` 0/2. Two of those over-report: `Op`'s functions are *used*, by
`Term.replaceKids` and `Term.indexAt?`, but not exposed (see below), and `InputParser`'s second hit
is `isDone`, a name the traversals share.

## Instantiation patterns

Kinds `INST_PATTERN`, `INST_NO_PATTERN`, `INST_ATTRIBUTE`, `INST_PATTERN_LIST`, `INST_POOL`,
`INST_ADD_TO_POOL` — the annotations a quantifier can carry as a third child, steering how cvc5
instantiates it.

The quantifiers themselves are done: `FORALL` and `EXISTS` in
`Cvc/{Untyped,Typed}/Theory/Quant.lean` (`mkForall`/`mkExists` over `BVars`, `forallH`/`existsH`
over a Lean function, and `smt! ∀`/`∃`), and `SET_COMPREHENSION` as `setComprehension` in each
layer's `Theory/Set`. Patterns would be an optional argument to `mkForall`/`mkExists`, sort-erased
in both layers since a pattern's terms are of mixed sorts.

`WITNESS` is **deliberately not wrapped**: asserting a term containing one aborts the process, see
[Cvc5Issues.md](Cvc5Issues.md).

## Parser

`InputParser` (10): `ofSolver`, `ofSolverAndSM`, `setFileInput`, `setStringInput`,
`setIncrementalStringInput`, `appendIncrementalStringInput`, `nextTerm`, `nextCommand`, `isDone`,
`getSymbolManager`.

`SymbolManager` (3): `getDeclaredSorts`, `getDeclaredTerms`, `getNamedTerms`.

`Command` (2): `getCommandName`, `invoke`.

lean-cvc5's own README lists parser stream input as a known gap on its side too.

## Relations and tables

**Nothing missing.** All fifteen `RELATION_*`/`TABLE_*` kinds are wrapped in both layers, the set
and bag operators are restated at the relation and table indices, the aggregates take their folding
function as a term, and projection is typed by a `Cols` spine of positions.

Kept out deliberately: `setMap`/`setFold`/`bagMap`/`bagFold`, whose results are arbitrary
containers rather than relations or tables — `relToSet`/`tableToBag` reach them.

The design is documented in `CLAUDE.md`'s "Relations and tables" section rather than here, so that
there is one copy of it. This entry exists to record that the area is closed.

## Tuple projection

Not a gap against lean-cvc5 — everything is reachable sort-erased — and no longer a gap at all for
the list-shaped index. What is left concerns the **product** index only, `Term (α × β)`.

**Sort-erased: done.** `Untyped.Term.tupleSelect i t` answers the component at its own sort. A
tuple sort *is* a datatype, so it is that datatype's selector under the hood, which is why cvc5
prints it `((_ tuple.select i) t)`. Unlike `getTupleValue` it builds a term, so it works on a
symbolic tuple and reads back through a model.

**`tupleProject` answers a tuple, never a component.** Projecting `#[1]` out of
`(Tuple Int Bool String)` gives `(Tuple Bool)`, and `#[2, 0]` gives `(Tuple String Int)`; it
reorders and duplicates as well as selects.

**Typed, at the `Tup α β` index: done** — `Term.tupAt` for a component, `tupProject` for a
selection, over `Col`/`Cols`. See `CLAUDE.md`'s "Relations and tables" section.

**Typed, at the `α × β` index: `fst` and `snd` only.** They read a tuple as Lean's
`Prod.fst`/`Prod.snd` read a product, which is what makes them work at every arity.
Right-flattening means `Term (α × β)` describes a longer tuple whenever `β` is a product, with `β`
covering *all* the remaining components — so `snd` of an `α × β × γ` answers the tuple
`(Tuple β γ)`, never component 1 alone. Sorts and claimed indices agree at every arity, and `snd`
composes to walk the tail.

What is missing there is **a single component out of the middle of a longer tuple** — the third of
four, say. It cannot be `snd`-then-`fst` when the position is past the second, and a family of
`tupleSelectN` was tried and dropped: making it sound needs a flatness side condition on the
trailing index, which pins each selector to one exact arity and puts a proof obligation in the
user's way. Signatures of the form `Term (α₀ × α₁ × rest) → Env (Term α₁)` were judged no better.

So the open problem is a type-level "nth component of a product" that neither restricts the arity
nor surfaces a proof obligation — and it is open only because the product index has no terminator.
The list-shaped index has one, which is exactly why `Col` works there and nothing analogous works
here. That is one more entry on the list of things the two encodings decide differently; see the
Tuples section of `CLAUDE.md`.

Sort-erased `tupleSelect` followed by `typeCheck` is the way to a middle component of a
product-indexed tuple meanwhile.

## Separation logic

**Nothing missing.** All five kinds and all five functions are wrapped in both layers, in
`Cvc/{Untyped,Typed}/Theory/Sep.lean`. `declareSepHeap` answers a **handle** carrying the heap's
location and data sorts, and `pto`/`nil` come off it — sort-erased it checks them, typed they are
indices. See `CLAUDE.md`'s "Separation logic" section.

The limitation once recorded here — that a heap's location sort is naturally *uninterpreted* and
`Typ` had no case for one — is closed: `Typ.uninterpreted` carries the name and `Srt.uninterpreted`
registers the sort, so a typed heap's locations can be an uninterpreted sort like any other index.

## Proof inspection

**Nothing missing.** `Solver.Proof` wraps cvc5's, indexed by the solver that produced it, with
`getRule`, `getResult`, `getArguments`, `getChildren`, `getRewriteRule?`/`getRewriteRule` and
`toString` in both layers, and `Solver.proofToString` beside them. See `CLAUDE.md`'s "Proofs"
section for the design, including the two hazards it documents.

## Operator reflection

`Term.getOp`, `Term.hasOp`, `Op.isIndexed`, `Op.getNumIndices`, `TermManager.mkOpOfString`.

Indexed terms can be built — the generator makes the `Op` inside the body, and `Term.replaceKids`
reuses a term's own — and taken apart, the views reading each index through `Term.indexAt?`. Those
call `getOp`, `isIndexed` and `getNumIndices` internally, which is why the namespace count above
reads complete; what is missing is `Op` itself as a value.

See also the `Op` TODO in `CLAUDE.md`: `Op` is `export`ed rather than wrapped, so it carries
cvc5's null-backed `Inhabited` and `(default : Op)` is a null. Wrapping `Op` would close both.

## Uninterpreted-sort values

Kind `UNINTERPRETED_SORT_VALUE`; `Term.isUninterpretedSortValue`,
`Term.getUninterpretedSortValue`.

`Srt.uninterpreted` exists, so sorts can be declared; their values cannot be read back.

## Cardinality constraints

Kind `CARDINALITY_CONSTRAINT`; `TermManager.mkCardinalityConstraint`,
`Term.getCardinalityConstraint`.

## Pools and oracles

`Solver.declarePool`, `Solver.declareOracleFun`.

## Odds and ends

- `Solver.simplify`.
- `TermManager.mkFiniteFieldElemOfString` — the string form; `mkFiniteFieldElem` is wrapped.
- `TermManager.mkOpOfString`.
- Kind `SEXPR`.
- `TermManager.mkFloatingPointOfComponents` — **deliberately skipped**, it duplicates the
  `fpOfBits` operator.
- `mkNullableLift` at an arbitrary `Kind` — **deliberately not exposed**. Every generated `<id>?`
  *is* a `nullable.lift`, so the capability is there; handing a caller a raw `Kind` is what we
  chose against, because cvc5 validates nothing and `mkNullableLift .NOT #[x, y]` builds a
  malformed term without complaint.

## Not bound by lean-cvc5 either

Statistics, option info, driver options, plugins. Nothing to wrap until lean-cvc5 binds them.

## Deliberately excluded

- **Skolems** — `TermManager.mkSkolem`, `getNumIndicesForSkolemId`, `Term.isSkolem`,
  `getSkolemId`, `getSkolemIndices`, kinds `SKOLEM` and `SKOLEM_ADD_TO_POOL`. Internal API.
- **`WITNESS`** — asserting a term containing one aborts the process rather than throwing.
- **Null-pointer checks** — every `isNull`. See the "null means two unrelated things in cvc5"
  section of `CLAUDE.md`. An absent `isNull` is the policy, not a gap.

## Not gaps, though a naive name diff flags them

- `getInterpolantSimple`/`OfGrammar`, `getAbductSimple`/`OfGrammar`,
  `synthFunWith`/`WithoutGrammar`, `findSynthWith`/`WithoutGrammar` — lean-cvc5's own internals
  behind the public `getInterpolant`/`getAbduct`/`synthFun`/`findSynth`, which this library calls
  and folds into an `Option Grammar` argument.
- `Term.andTerm`/`orTerm`/`xorTerm`/`eqTerm`/`impTerm`/`iteTerm`/`notTerm` — cvc5's Boolean
  convenience methods, covered by the generated `and`/`or`/… operators.
- Kinds `CONST_ROUNDINGMODE`, `CONST_FINITE_FIELD`, `VARIABLE` — covered by the hand-written
  `mkRoundingMode`, `mkFiniteFieldElem` and `mkBVar`, which never name the kind.
- `Term.getNumChildrenInternal`, `Term.isCardinalityConstraintInternal` — internal.
- 23 of the enum variants a `Kind.lean` scan turns up are `SortKind`, not term kinds, and four
  more (`INTERNAL_KIND`, `LAST_KIND`, `UNDEFINED_KIND`, `NULL_TERM`) are sentinels.

## Regenerating the counts

Run these from the repository root: their paths are relative to it, not to this file.

Namespace coverage — every lean-cvc5 declaration whose name appears nowhere in the non-test
source. It over-reports (folded aliases) and can under-report where a name is shared across
namespaces, so triage the output against the two sections above:

```bash
python3 - <<'PY'
import re, pathlib, subprocess
src = pathlib.Path(".lake/packages/cvc5/cvc5.lean").read_text().splitlines()
stack=[]; decls={}
for ln in src:
    m=re.match(r"^namespace\s+([\w.']+)\s*$", ln)
    if m: stack.append(m.group(1)); continue
    m=re.match(r"^end\s+([\w.']+)\s*$", ln)
    if m and stack and stack[-1]==m.group(1): stack.pop(); continue
    pat = r"^\s*(?:private\s+)?(?:protected\s+)?(?:extern_def[!?]*|opaque|def)\s+([\w']+)\s*[:(]"
    m=re.match(pat, ln)
    if m and stack:
        if m.group(1) in ("null","isNull","beq","hash","toString"): continue
        decls.setdefault(stack[-1],set()).add(m.group(1))
src = subprocess.run(["bash","-c","cat $(find Cvc -name '*.lean')"],
                       capture_output=True, text=True).stdout
for ns in sorted(decls):
    if ns in {"EnvT","cvc5"}: continue
    miss = sorted(n for n in decls[ns] if not re.search(r"\b"+re.escape(n)+r"\b", src))
    tail = f"  MISSING: {' '.join(miss)}" if miss else ""
    print(f"{ns}: {len(decls[ns])-len(miss)}/{len(decls[ns])}{tail}")
PY
```

Term-kind coverage — note `Kind.lean` holds both `Kind` and `SortKind`, so the split matters:

```bash
python3 - <<'PY'
import re, pathlib, subprocess
txt = pathlib.Path(".lake/packages/cvc5/cvc5/Kind.lean").read_text()
kind = set(re.findall(r"^  \| ([A-Z][A-Z0-9_]*)$", txt[:txt.index("inductive SortKind")], re.M))
src = subprocess.run(["bash","-c","cat $(find Cvc -name '*.lean')"],
                     capture_output=True, text=True).stdout
un = sorted(k for k in kind if not re.search(r"\b"+k+r"\b", src))
print(f"{len(kind)-len(un)}/{len(kind)} referenced; {len(un)} not:"); print(" ".join(un))
PY
```

Note it scans comments as well as code, so a kind named in a commented-out block counts as
referenced.
