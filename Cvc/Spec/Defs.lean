/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public meta import Lean.Elab.Command



/-! # Term-creation specification

This module defines the data describing how to build the term constructors for a cvc5 term kind,
and the environment extension storing that data.

A specification entry is written once, in the *typed* form, and describes everything both layers
need:

- the sort shape of each argument and of the result,
- the type and size variables the operator is polymorphic in, with their refinement classes,
- which n-ary variants to generate.

The untyped signature is *derived* from the typed one by erasure: every shape becomes a plain
`Untyped.Term`. See `Cvc.Gen` for the generators.
-/
namespace Cvc public meta section

open Lean



/-- Natural-number expression describing a sort index, such as a bit-vector size.

Size variables are bound by the enclosing `OpSpec`, either as a size binder or as an operator
index. Arithmetic is needed by operators whose result index is computed: `BITVECTOR_CONCAT` sums
its arguments' sizes, `BITVECTOR_EXTRACT` yields `hi - lo + 1`, `BITVECTOR_REPEAT` yields `n * k`.

Subtraction is `Nat` subtraction, so it truncates at zero.
-/
inductive SizeExpr
  /-- Literal size. -/
  | lit (n : Nat)
  /-- Size variable, bound by the enclosing `OpSpec`. -/
  | var (name : Name)
  /-- Sum of two sizes. -/
  | add (lft rgt : SizeExpr)
  /-- Truncated difference of two sizes. -/
  | sub (lft rgt : SizeExpr)
  /-- Product of two sizes. -/
  | mul (lft rgt : SizeExpr)
  /-- The operator's own arity: how many term arguments it was applied to.

  `BITVECTOR_FROM_BOOLS` builds a bit-vector one bit per argument, so its result's size is not a
  function of its arguments' sorts but of how many there are. In the fixed-arity constructor this
  is a literal; in the n-ary one it is the term array's size, which makes that signature depend on
  a runtime value.
  -/
  | arity
deriving Inhabited, Repr, BEq

namespace SizeExpr

/-- Size variables occurring in a size expression. -/
partial def vars : SizeExpr → Array Name
  | lit _ | arity => #[]
  | var n => #[n]
  | add l r | sub l r | mul l r => l.vars ++ r.vars

end SizeExpr



/-- Sort shape: `Typ` extended with type variables and size arithmetic.

A shape describes the sort of an argument or result *as the typed layer sees it*. Two operations
are defined on shapes:

- **erasure**, which forgets the shape entirely and yields the untyped signature, where every
  argument and the result are plain `Untyped.Term`s;
- **rendering**, which turns the shape into the Lean type indexing a `Typed.Term`.
-/
inductive Shape
  /-- Type variable, bound by the enclosing `OpSpec`. -/
  | var (name : Name)
  /-- SMT-LIB `Bool`, rendered as `Bool`. -/
  | bool
  /-- SMT-LIB `Int`, rendered as `Int`. -/
  | int
  /-- SMT-LIB `Real`, rendered as `Rat`. -/
  | real
  /-- SMT-LIB `String`, rendered as `String`. -/
  | string
  /-- SMT-LIB `RegLan`, rendered as `Regex`. -/
  | regex
  /-- SMT-LIB `RoundingMode`, rendered as `Float.RoundingMode`. -/
  | roundingMode
  /-- SMT-LIB bit-vector, rendered as `BitVec size`. -/
  | bitVec (size : SizeExpr)
  /-- SMT-LIB floating point, rendered as `Float exp sig`. -/
  | float (exp sig : SizeExpr)
  /-- SMT-LIB finite field, rendered as `FiniteField size`. -/
  | finiteField (size : SizeExpr)
  /-- SMT-LIB sequence, rendered as `Array elm`. -/
  | seq (elm : Shape)
  /-- SMT-LIB set, rendered as `Set elm`; requires `Ord` on `elm`. -/
  | set (elm : Shape)
  /-- SMT-LIB bag, rendered as `Bag elm`; requires `Ord` on `elm`. -/
  | bag (elm : Shape)
  /-- SMT-LIB array, rendered as `TotalMap idx elm`; requires `Ord` on `idx`. -/
  | array (idx elm : Shape)
  /-- SMT-LIB function, rendered as the Lean arrow `dom → cod`.

  Curried: `fn α (fn β γ)` describes the SMT sort `(-> α β γ)`.
  -/
  | fn (dom cod : Shape)
deriving Inhabited, Repr, BEq

namespace Shape

/-- Type variables occurring in a shape. -/
partial def typeVars : Shape → Array Name
  | var n => #[n]
  | bool | int | real | string | regex | roundingMode => #[]
  | bitVec _ | float .. | finiteField _ => #[]
  | seq e | set e | bag e => e.typeVars
  | array i e | fn i e => i.typeVars ++ e.typeVars

/-- Size variables occurring in a shape. -/
partial def sizeVars : Shape → Array Name
  | var _ => #[]
  | bool | int | real | string | regex | roundingMode => #[]
  | bitVec w => w.vars
  | float e s => e.vars ++ s.vars
  | finiteField s => s.vars
  | seq e | set e | bag e => e.sizeVars
  | array i e | fn i e => i.sizeVars ++ e.sizeVars

/-- Type variables that need an `Ord` instance, because they index a `Set`, `Bag` or `TotalMap`.

`Set`, `Bag` and `TotalMap` are `Std.TreeSet`/`Std.TreeMap` wrappers, so their element (respectively
index) type must be ordered.
-/
partial def ordVars : Shape → Array Name
  | var _ => #[]
  | bool | int | real | string | regex | roundingMode => #[]
  | bitVec _ | float .. | finiteField _ => #[]
  | seq e => e.ordVars
  | set e | bag e => e.typeVars ++ e.ordVars
  | array i e => i.typeVars ++ i.ordVars ++ e.ordVars
  | fn d c => d.ordVars ++ c.ordVars

end Shape



/-- Unit element used by an n-ary operator's `N'` variant on an empty term array. -/
inductive NaryUnit
  /-- Boolean literal, built with `Term.mkBool`. -/
  | bool (b : Bool)
  /-- Integer literal, built with `Term.mkInt`. -/
  | int (i : Int)
deriving Inhabited, Repr, BEq

/-- Whether, and how, to generate n-ary variants of an operator. -/
inductive Nary
  /-- Fixed arity only. -/
  | never
  /-- Also generate `<id>N`, taking a term array with at least two elements. -/
  | array
  /-- Also generate `<id>N` and `<id>N'`, the latter defaulting on 0- and 1-element arrays. -/
  | arrayWithUnit (unit : NaryUnit)
deriving Inhabited, Repr, BEq



/-- Associativity of an infix notation. -/
inductive Assoc
  /-- Left-associative: `a - b - c` is `(a - b) - c`. -/
  | left
  /-- Right-associative: `a ∧ b ∧ c` is `a ∧ (b ∧ c)`. -/
  | right
deriving Inhabited, Repr, BEq

/-- Surface notation for an operator in the `smt!` DSL.

The generated grammar rule is named `…smtOp.<shape>.<id>`, and the expander in `Cvc.Ext`
dispatches on the last three components of that node kind. That convention is what lets the
grammar be generated per theory while the expansion logic stays written once.
-/
inductive Notation
  /-- No surface notation; the operator is reachable as a function only. -/
  | none
  /-- Prefix notation such as `¬ t`, with the rule's precedence and its argument's. -/
  | pref (sym : String) (prec argPrec : Nat)
  /-- Infix notation such as `a ∧ b`.

  When the operator also has an n-ary variant, the bracket form `sym[a, b, …]` is generated
  alongside and expands to the `N` function.
  -/
  | inf (sym : String) (prec : Nat) (assoc : Assoc)
deriving Inhabited, Repr, BEq

namespace Notation

/-- The symbol of a notation, if any. -/
def sym? : Notation → Option String
  | none => Option.none
  | pref s .. | inf s .. => some s

end Notation



/-- A value parameter: a plain Lean argument, passed to the constructor as-is.

Constructors take data that is not a term — the `Bool` of a boolean literal, the `String` of a
symbol's name, the numeral behind a bit-vector. Such a parameter is emitted unchanged in both
layers, since there is no sort to erase.
-/
structure ValArg where
  /-- Name of the generated parameter. -/
  name : Name
  /-- Lean type of the parameter, emitted verbatim. -/
  type : Name
deriving Inhabited, Repr, BEq

/-- One argument of an operator. -/
structure Arg where
  /-- Name of the generated parameter. -/
  name : Name
  /-- Sort shape of the argument. -/
  shape : Shape
deriving Inhabited, Repr, BEq

/-- A type variable of an operator, together with the refinement classes it must satisfy.

Refinement classes are emitted as instance binders by the typed generator and dropped by the
untyped one, which has no index to constrain.
-/
structure TyVar where
  /-- Name of the type variable. -/
  name : Name
  /-- Refinement classes, such as `IsArith`. -/
  classes : Array Name := #[]
deriving Inhabited, Repr, BEq

/-- Everything needed to generate the typed and untyped constructors for one term kind.

The entry is keyed by `id`, the name of the generated function; `kind` is the `cvc5.Kind`
constructor the term is built with, and is checked to exist when the entry is declared.
-/
structure OpSpec where
  /-- Name of the generated function, such as `and`. -/
  id : Name
  /-- Constructor of `cvc5.Kind`, such as `AND`.

  For an entry built by a `TermManager` method this is still the kind the resulting term *has*,
  even though the term is not built by applying it.
  -/
  kind : Name
  /-- `TermManager` method building the term, when it is not built by applying `kind`.

  Nullary constants have no `mkTerm` form: `SET_EMPTY` is `mkEmptySet`, `PI` is `mkPi`, and so on.
  Where the sort cannot be inferred from the arguments, the generated function takes one `Srt` per
  type variable the arguments leave free and builds what the method wants from those.
  -/
  tmFn : Option Name := none
  /-- Shape whose sort the `tmFn` *method* wants, when it is not the result's own.

  This does not reach the generated signature. A constructor always takes the sorts of the type
  variables its arguments leave free — the element sorts — and the generator builds what cvc5 asks
  for out of them. Most methods want the sort of the term they build; `mkEmptySequence` wants the
  element sort instead, which is what this records.
  -/
  sortArg : Option Shape := none
  /-- Docstring of the generated fixed-arity function. -/
  doc : String
  /-- Type variables, with their refinement classes. -/
  tyVars : Array TyVar := #[]
  /-- Size variables, bound as implicit `Nat`s and inferred from the arguments. -/
  sizeVars : Array Name := #[]
  /-- Operator indices, bound as explicit `Nat`s ahead of the term arguments.

  An indexed operator is built by applying an `Op` carrying these values, rather than by applying
  the kind directly. They are what SMT-LIB writes as `(_ extract hi lo)`.
  -/
  indices : Array Name := #[]
  /-- Value parameters, in order, ahead of the term arguments. -/
  valArgs : Array ValArg := #[]
  /-- Arguments, in order. -/
  args : Array Arg := #[]
  /-- Sort shape of the result. -/
  ret : Shape
  /-- Which n-ary variants to generate. -/
  nary : Nary := .never
  /-- Name of the n-ary variant, when `<id>N` is not the right one.

  The `N` suffix suits an operator whose n-ary form is the same operation at greater arity. It
  does not suit one where the distinction is singular versus plural: `bvFromBool` takes a bit and
  `bvFromBools` takes several.
  -/
  naryName : Option Name := none
  /-- Surface notation in the `smt!` DSL. -/
  smtNotation : Notation := .none
  /-- Module the entry was declared in, so that a generator can select a whole theory. -/
  declaredIn : Name := .anonymous
  /-- Declaration order, so that generated constructors come out in specification order. -/
  order : Nat := 0
deriving Inhabited, Repr

namespace OpSpec

/-- Type variables that need an `Ord` instance, across all arguments and the result. -/
def ordVars (spec : OpSpec) : Array Name :=
  let fromArgs := spec.args.flatMap (Shape.ordVars ·.shape)
  (fromArgs ++ spec.ret.ordVars).foldl
    (fun acc n => if acc.contains n then acc else acc.push n)
    #[]

/-- Type variables occurring in the result but in no argument.

Such a variable is lost by erasure: the untyped constructor takes the result sort explicitly while
the typed one recovers it from its index. Applying a kind always infers the sort from the
arguments, so this is empty for every `kind`-built entry, and `op%` rejects one where it is not.
It is exactly the constructors — the `tmFn` entries — that need it.
-/
def unboundRetVars (spec : OpSpec) : Array Name :=
  let bound := spec.args.flatMap (Shape.typeVars ·.shape)
  spec.ret.typeVars.filter (! bound.contains ·)

/-- Whether the operator has a version lifted over nullables.

`mkNullableLift` takes a `Kind` and the terms to apply it to, and nothing else, which is what
decides this:

- a **constructor** is out — it has no term argument to be null, and it builds through a
  `TermManager` method rather than a kind;
- an **indexed** operator is out — it is applied through an `Op` carrying its indices, and there is
  no way to hand one to `mkNullableLift`;
- **value parameters** are out for the same reason, having nowhere to go in the lifted lambda. They
  only ever occur on constructors, so this rules nothing else out.
-/
def isLiftable (spec : OpSpec) : Bool :=
  spec.tmFn.isNone && spec.indices.isEmpty && spec.valArgs.isEmpty && !spec.args.isEmpty

end OpSpec



/-- Environment extension holding every declared `OpSpec`, keyed by `OpSpec.id`.

Entries are added by the `op%` command and read by `gen_untyped%`/`gen_typed%`. Going through an
extension is what lets the specification live in one module while generation happens in per-theory
modules of both layers.
-/
initialize opSpecExt : SimplePersistentEnvExtension (Name × OpSpec) (Std.HashMap Name OpSpec) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun map (id, spec) => map.insert id spec
    addImportedFn := fun entriess =>
      entriess.foldl
        (fun map entries => entries.foldl (fun map (id, spec) => map.insert id spec) map)
        {}
  }

/-- Registers an operator specification. -/
def registerOpSpec [Monad m] [MonadEnv m] (spec : OpSpec) : m Unit :=
  modifyEnv (opSpecExt.addEntry · (spec.id, spec))

/-- Looks an operator specification up by name. -/
def findOpSpec? [Monad m] [MonadEnv m] (id : Name) : m (Option OpSpec) := do
  return opSpecExt.getState (← getEnv) |>.get? id

/-- Number of registered specifications, used to stamp declaration order. -/
def opSpecCount [Monad m] [MonadEnv m] : m Nat := do
  return opSpecExt.getState (← getEnv) |>.size

/-- Every specification declared in a module, in declaration order. -/
def opSpecsOf [Monad m] [MonadEnv m] (mod : Name) : m (Array OpSpec) := do
  let all := opSpecExt.getState (← getEnv) |>.toArray.map (·.2)
  return all.filter (·.declaredIn == mod) |>.qsort (·.order < ·.order)
