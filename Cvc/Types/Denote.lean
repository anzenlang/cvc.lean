/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Srt
public import Cvc.Types.Set
public import Cvc.Types.Bag
public import Cvc.Types.Array
public import Cvc.Types.Tuple
public import Cvc.Types.Record
public import Cvc.Types.Float
public import Cvc.Types.FiniteField

-- for the delaborator, which shows a denotation as the type it reduces to
public meta import Lean.Meta.Tactic.Simp.Main
public meta import Lean.PrettyPrinter.Delaborator.Basic



/-! # The Lean type a sort denotes

`Typ.Denote τ` is the Lean type that indexes terms of sort `τ`: `.int` denotes `Int`, `.set .int`
denotes `Set Int`, a record its `Record`, a tuple its product. It is what makes a sort carried as
data — a `Typ` field of a term's view — usable as a term's index: matching the `Typ` refines
`Term τ.Denote` to `Term Int`, definitionally.

A sort with no better denotation denotes `Sorted τ`, a stand-in indexed by the sort itself: declared
sorts, a container keyed on something with no order, a tuple whose last component is a tuple. A
term at a stand-in is moved to a user's own index with `Typed.Term.cast`.

Everything here is reducible and exposed, so that a known `Typ` reduces both in unification and in
instance resolution.
-/

namespace Cvc public section

/-- The stand-in Lean type for a sort with no better denotation, indexed by the sort itself. -/
structure Sorted (τ : Typ) : Type where
  private mk ::

instance : ToTyp (Sorted τ) := ⟨τ⟩

/-- `Sorted τ` has exactly one value, so the constant order is the right one. -/
instance : Ord (Sorted τ) := ⟨fun _ _ => .eq⟩

/-- Whether a tuple's last component is itself a tuple. -/
@[expose, reducible] def Typ.lastIsProd : List Typ → Bool
  | [] => false
  | [.prod _] => true
  | [_] => false
  | _ :: rest => Typ.lastIsProd rest

mutual

/-- The Lean type a sort denotes, together with its order if it has one.

Computed together because a container's denotation needs its element's order: `.set .int` denotes
`Set Int`, which is only a type given `Ord Int`. A container whose element has no order — a set of
functions — denotes `Sorted τ`, as do declared sorts. `TotalMap` and functions have no order of
their own; a record or a tuple has one exactly when all its components do, lexicographically, as
`OrdFields` and the product order give it.
-/
@[expose, reducible] def Typ.denoteWithOrd : Typ → (T : Type) × Option (Ord T)
  | .bool => ⟨Bool, some inferInstance⟩
  | .int => ⟨Int, some inferInstance⟩
  | .real => ⟨Rat, some inferInstance⟩
  | .string => ⟨String, some inferInstance⟩
  | .regex => ⟨Regex, some inferInstance⟩
  | .roundingMode => ⟨Cvc.Float.RoundingMode, some inferInstance⟩
  | .bitVec n => ⟨BitVec n, some inferInstance⟩
  | .float e s => ⟨Cvc.Float e s, some inferInstance⟩
  | .finiteField n => ⟨FiniteField n, some inferInstance⟩
  | .seq e => match e.denoteWithOrd with
    | ⟨T, some _⟩ => ⟨Array T, some inferInstance⟩
    | ⟨T, none⟩ => ⟨Array T, none⟩
  | .nullable e => match e.denoteWithOrd with
    | ⟨T, some _⟩ => ⟨Option T, some inferInstance⟩
    | ⟨T, none⟩ => ⟨Option T, none⟩
  | .record fs => match Typ.denoteFieldsWithOrd fs with
    | ⟨Fs, some _⟩ => ⟨Record Fs, some inferInstance⟩
    | ⟨Fs, none⟩ => ⟨Record Fs, none⟩
  | .prod ts => Typ.denoteProdWithOrd ts
  | .set e => match e.denoteWithOrd with
    | ⟨T, some _⟩ => ⟨Set T, some inferInstance⟩
    | ⟨_, none⟩ => ⟨Sorted (.set e), some inferInstance⟩
  | .bag e => match e.denoteWithOrd with
    | ⟨T, some _⟩ => ⟨Bag T, some inferInstance⟩
    | ⟨_, none⟩ => ⟨Sorted (.bag e), some inferInstance⟩
  | .arrayTo i e => match i.denoteWithOrd, e.denoteWithOrd with
    | ⟨I, some _⟩, ⟨E, _⟩ => ⟨TotalMap I E, none⟩
    | ⟨_, none⟩, _ => ⟨Sorted (.arrayTo i e), some inferInstance⟩
  | .function d c => ⟨d.denoteWithOrd.1 → c.denoteWithOrd.1, none⟩
  | τ => ⟨Sorted τ, some inferInstance⟩

/-- A record's fields' denotations, by name, with the record's order if every field has one. -/
@[expose, reducible] def Typ.denoteFieldsWithOrd
: List (String × Typ) → (Fs : List (String × Type)) × Option (OrdFields Fs)
  | [] => ⟨[], some inferInstance⟩
  | (n, t) :: rest => match t.denoteWithOrd, Typ.denoteFieldsWithOrd rest with
    | ⟨T, some _⟩, ⟨Fs, some _⟩ => ⟨(n, T) :: Fs, some inferInstance⟩
    | ⟨T, _⟩, ⟨Fs, _⟩ => ⟨(n, T) :: Fs, none⟩

/-- A tuple's denotation: the right-nested product of its components', as `α × β × γ` indexes a
three-component tuple, and `OneTuple` for one component; ordered if every component is.

A tuple whose last component is itself a tuple has no product to denote it — the product would
flatten it — and neither has the empty tuple: those are `Sorted`.
-/
@[expose, reducible] def Typ.denoteProdWithOrd : List Typ → (T : Type) × Option (Ord T)
  | [] => ⟨Sorted (.prod []), some inferInstance⟩
  | [t] => match t.denoteWithOrd with
    | ⟨T, some _⟩ => ⟨OneTuple T, some inferInstance⟩
    | ⟨T, none⟩ => ⟨OneTuple T, none⟩
  | [a, .prod bs] => ⟨Sorted (.prod [a, .prod bs]), some inferInstance⟩
  | [a, b] => match a.denoteWithOrd, b.denoteWithOrd with
    | ⟨A, some _⟩, ⟨B, some _⟩ => ⟨A × B, some inferInstance⟩
    | ⟨A, _⟩, ⟨B, _⟩ => ⟨A × B, none⟩
  | a :: b :: c :: rest =>
    if Typ.lastIsProd (c :: rest) then ⟨Sorted (.prod (a :: b :: c :: rest)), some inferInstance⟩
    else match a.denoteWithOrd, Typ.denoteProdWithOrd (b :: c :: rest) with
      | ⟨A, some _⟩, ⟨B, some _⟩ => ⟨A × B, some inferInstance⟩
      | ⟨A, _⟩, ⟨B, _⟩ => ⟨A × B, none⟩

/-- `Typ.denoteWithOrd` lifted to `Typ?`. An abstract sort is never a term's, so it denotes nothing.
-/
@[expose, reducible] def Typ?.denoteWithOrd : Typ? → (T : Type) × Option (Ord T)
  | .typ t => t.denoteWithOrd
  | _ => ⟨Empty, none⟩

end

/-- A record's fields' denotations, by name. -/
@[expose, reducible] def Typ.denoteFields (fs : List (String × Typ)) : List (String × Type) :=
  (Typ.denoteFieldsWithOrd fs).1

/-- A tuple's denotation; see `Typ.denoteProdWithOrd`. -/
@[expose, reducible] def Typ.denoteProd (ts : List Typ) : Type := (Typ.denoteProdWithOrd ts).1

/-- The Lean type a sort denotes.

It reduces on a known `Typ`, which is what makes matching on a view's `Typ` refine the kids'
index: `Term (Typ.Denote .int)` *is* `Term Int`, and `Term (Typ.Denote (.set .int))` is
`Term (Set Int)`, with the very `Ord Int` a user's `Set Int` has.

Reducible, as is everything it is computed with, so that instance resolution sees through it too: a
record's `FieldOf` instances are found on the field list it reduces to.
-/
@[expose, reducible] def Typ.Denote (τ : Typ) : Type := τ.denoteWithOrd.1

/-- A denotation's sort is the sort it denotes. -/
instance (τ : Typ) : ToTyp τ.Denote := ⟨τ⟩

/-- The function type from the denotations of `doms`, in order, to `β`. -/
@[expose] def Typ.arrows : List Typ → Type → Type
  | [], β => β
  | τ :: τs, β => τ.Denote → Typ.arrows τs β

/-- A function type over denotations has the function sort they denote. -/
instance Typ.arrowsToTyp [ToTyp β] : (doms : List Typ) → ToTyp (Typ.arrows doms β)
  | [] => inferInstanceAs (ToTyp β)
  | τ :: τs =>
    have : ToTyp (Typ.arrows τs β) := Typ.arrowsToTyp τs
    inferInstanceAs (ToTyp (τ.Denote → Typ.arrows τs β))

open Lean PrettyPrinter Delaborator SubExpr in
/-- Shows a denotation, or a function type over denotations, as the type it reduces to.

`Typ.Denote (.set .int)` is `Set Int`, and a reader should see `Set Int`. It reduces by `dsimp`
with the denotation's own definitions only: `whnf` would also unfold `Set`, an abbreviation, and
show `Std.TreeSet Int compare`. A sort bound by an unmatched pattern does not reduce, or only
part-way: the guards hand it back to the default printer, `τ.Denote`, rather than show it stuck
inside `denoteWithOrd` — and without them the delaborator would re-enter itself forever.
-/
@[delab app.Cvc.Typ.Denote, delab app.Cvc.Typ.arrows]
public meta def delabDenote : Delab := do
  let e ← getExpr
  let mut thms : Meta.SimpTheorems := {}
  for n in [``Typ.Denote, ``Typ.denoteWithOrd, ``Typ?.denoteWithOrd, ``Typ.arrows,
      ``Typ.denoteFields, ``Typ.denoteProd, ``Typ.denoteFieldsWithOrd, ``Typ.denoteProdWithOrd,
      ``Typ.lastIsProd] do
    thms ← thms.addDeclToUnfold n
  let ctx ← Meta.Simp.mkContext (simpTheorems := #[thms])
    (congrTheorems := ← Meta.getSimpCongrTheorems)
  let (e', _) ← Meta.dsimp (← instantiateMVars e) ctx
  guard <| e' != e
  guard <| !e'.hasExprMVar
  -- a sort that is a variable leaves the reduction stuck part-way, which says less than `τ.Denote`
  guard <| (e'.find? fun x =>
    x.isAppOf ``Typ.denoteWithOrd || x.isAppOf ``Typ?.denoteWithOrd ||
      x.isAppOf ``Typ.denoteFieldsWithOrd || x.isAppOf ``Typ.denoteProdWithOrd).isNone
  withTheReader SubExpr (fun c => { c with expr := e' }) delab


end

end Cvc
