# Problems in Lean itself

Sharp edges found in Lean — the language, its elaborator, the module system — while building
cvc.lean. Each entry is reproduced in a standalone Lake project with no dependency on cvc.lean, so
that it can be raised upstream as is.

This is the Lean counterpart of [Cvc5Issues.md](Cvc5Issues.md), which is about cvc5's C++ API.

Found against **Lean `v4.34.1`**, the library's toolchain; the code involved was checked unchanged
in `v4.35.0-rc4` and `v4.35.0`.

## Reproducing

A two-module project, built with `lake build Notes.B`:

```toml
# lakefile.toml
name = "notes"
[[lean_lib]]
name = "Notes"
```

```lean
-- Notes/A.lean
module
public noncomputable section

/-- A phantom index whose safety comes from its definition not being exposed. -/
def Sealed (_ : Type) : Type := String

/-- The same index as a one-field structure, for comparison. -/
structure Wrapped (_ : Type) where
  private mk ::
  private val : String

def useSealed (_ : Sealed Bool) : Unit := ()
def useWrapped (_ : Wrapped Bool) : Unit := ()
```

```lean
-- Notes/B.lean
module
import Notes.A
noncomputable section

example (x : Sealed Int) : Unit := useSealed x
example (x : Wrapped Int) : Unit := useWrapped x
```

## 1. A deliberately unexposed definition always comes with a hint to expose it

**Status: to raise on the Lean Zulip.** See "Action" below.

**Severity: user experience.** The error is right; the note appended to it points users at the one
thing a library built this way needs them not to do.

Output of the reproduction:

```
error: Notes/B.lean:5:45: Application type mismatch: The argument
  x
has type
  Sealed Int
but is expected to have type
  Sealed Bool
in the application
  useSealed x

Note: The following definitions were not unfolded because their definition is not exposed:
  Sealed ↦ 4
error: Notes/B.lean:6:47: Application type mismatch: The argument
  x
has type
  Wrapped Int
but is expected to have type
  Wrapped Bool
in the application
  useWrapped x
```

**Where it comes from.** `mkUnfoldAxiomsNote` in `src/lean/Lean/Meta/Check.lean`, called from
`mkHasTypeButIsExpectedMsg`. Whenever the current file is a module, it re-runs the failed
unification with diagnostics on and lists every constant that was imported as an axiom although
its original kind is a definition — which is exactly what a non-exposed `def` is. Nothing else
gates it: there is no option, and no attribute is consulted. `@[irreducible]` does not help either,
since the blocked unfold is recorded (`recordUnfoldAxiom`, in `Meta/GetUnfoldableConst.lean` and
`Meta/WHNF.lean`) before any transparency setting is looked at.

**Why it matters here.** cvc.lean's typed layer *is* this pattern. `Cvc.Typed.Term α` is a `def`
equal to the sort-erased `Cvc.Untyped.Term`, and the index `α` is phantom: what keeps a
`Term Int` from being passed where a `Term Bool` is expected is precisely that the definition is not
exposed to the user's module. Every sort error a user makes therefore ends with a note listing
`Term`, which reads as a suggestion that `import all` would fix it. It would — by switching the
safety off, after which `Term Int` and `Term Bool` are the same type. The note is accurate, but for
a definition sealed on purpose it is advice against the library's design, and new users are the
ones most likely to take it.

**What cvc.lean will not do.** The note is only given for constants of definition kind, so a
one-field structure — `Wrapped` above — gives the same error without it. Rewriting the phantom
types as structures is not an option for cvc.lean: the design relies on a typed term being
definitionally its sort-erased one (and the cvc5 term underneath), which is what makes the typed
layer a zero-cost re-typing of the sort-erased one and lets an array of typed terms be passed as an
array of sort-erased ones without a copy. That is the trade the note now taxes.

**What would fix it.** Any way for the author of a definition to say "not exposing this is
intentional, do not suggest otherwise":

- an attribute on the definition (say `@[sealed]`) that `mkUnfoldAxiomsNote` filters out, kept in
  the module's public data so that importers' error messages see it;
- or, less precisely, an option to turn the note off, which a library could not set on its users'
  behalf, so it helps only in documentation and tests.

The attribute is the one that solves the problem, since the note is generated in the user's module.

**Action: post on the Lean Zulip** (`#lean4`, or a module-system thread if one is active),
describing the pattern — a phantom index made safe by not exposing its definition — with the
reproduction above, and asking whether an attribute like the one sketched would be accepted, or
whether there is an intended way to express a deliberately sealed definition. Record the thread's
link and outcome in this entry once posted.
