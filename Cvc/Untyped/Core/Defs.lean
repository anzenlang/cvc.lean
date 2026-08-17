/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Defs
public import Cvc.Ext

import all Cvc.Basic.Env



/-! # The sort-erased term type

A term carries no sort on the Lean side: it is exactly a cvc5 term, so the wrapper is a zero-cost
`def` and the conversions either way are `id`. `def3%` derives the comparison and printing
instances from the underlying type.

`Cvc.Untyped.Term` names both this type and the namespace holding the generated
constructors. Being a *declaration* as well as a namespace is what lets a typed generation site
write

```lean
open Cvc renaming Untyped.Term → T
```

and have the generator's `T.<id>` delegation resolve.
-/
namespace Cvc.Untyped public section variable [Ω]

def3% Term ← cvc5.Term

/-- An array of sort-erased terms. -/
abbrev Terms := Array Term

namespace Term

/-! ## Substitution

cvc5 substitutes **simultaneously and once**: the sources are matched in a single pre-order pass,
so a replacement is never itself rewritten, and the result is not driven to a fixed point.
Substituting `x` by `g z` in `f x y` gives `f (g z) y` even when `z` is also a source.
-/

/-- Simultaneously replaces each `src[i]` by `tgt[i]` throughout `t`.

A source may be any sub-term, not only a variable, and one that does not occur leaves the term
unchanged. Where `src` holds duplicates the earliest wins. cvc5 reads the two arrays as a 1:1
mapping, which is what `valid` keeps true.

`substitute` is the same thing over pairs and is usually the one to reach for; this form exists
because the two arrays are what cvc5 takes.
-/
def substitute'
  (t : Term) (src tgt : Terms)
  (valid : src.size = tgt.size := by
    (try grind) <;> fail "failed to prove there are as many replacements as sub-terms")
: Env Term :=
  let _ := valid
  runUnsafe' do t.toUnsafe.substitute src tgt

/-- Simultaneously replaces the first of each pair by the second throughout `t`.

The pairs are applied in one pass, so a replacement is not itself rewritten by a later pair, and
the earliest pair wins where a sub-term appears as the source of more than one.
-/
def substitute (t : Term) (terms : Array (Term × Term)) : Env Term := do
  -- the arrays are built together, carrying the proof that they stay the same length
  let mut res : (src : Array Term) × (tgt : Array Term) ×' src.size = tgt.size :=
    ⟨Array.mkEmpty terms.size, Array.mkEmpty terms.size, rfl⟩
  for (from', to') in terms do
    let ⟨src, tgt, h⟩ := res
    res := ⟨src.push from', tgt.push to', by simp [h]⟩
  let ⟨src, tgt, valid⟩ := res
  t.substitute' src tgt valid

end Term

namespace Terms

private def toUnsafe : Terms → Array cvc5.Term := id
private def ofUnsafe : Array cvc5.Term → Terms := id

private example (ts : Terms) : ofUnsafe ts.toUnsafe = ts := rfl

end Terms

/-- Sort-erased `smt!`.

`scoped`, so that `open Cvc.Untyped` selects this layer's DSL. It forwards to `smtU!`, which
expands to fully-qualified `Cvc.Untyped.Term.…` calls; nothing needs to be in scope.
-/
scoped syntax "smt! " ppLine group(colGt smtTerm) : term

macro_rules | `(smt! $t:smtTerm) => `(smtU! $t)
