/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public meta import Lean.Elab.Command
public import Cvc.Gen.View
import all Cvc.Spec.Defs



/-! # Generating typed views

A theory's typed view is indexed by the sort it takes apart: `Cvc.Typed.View.Arith : Typ → Type`.
It is built in two layers.

- **Parts.** For each sort the theory's operators produce, an inductive of those operators:
  `View.Arith.OnBool`, `OnInt`, `OnRat`, and `OnAny β` for those producing a type variable —
  `ite`, or `add` at `{α : IsArith}`. A constructor has its operator's indices, then the size and
  type variables its result does not fix, read off the kids' sorts, then implicit proofs — a type
  variable's classes as the `Typ` predicate each stands for, a computed result's equation with the
  part's parameter, `n + m = w` for a concatenation — then its kids, typed. A kid whose sort
  mentions a type variable is indexed by `Typ.Denote` of that sort.
- **The theory view**, one constructor per part, at the part's sort:
  `bool (v : OnBool) : View .bool`, `bitVec (w) (v : OnBitVec w) : View (.bitVec w)`,
  `any (v : OnAny τ.Denote) : View τ`. Matching an operator refines the sort to the part's; a
  compound result's equation stays a proof field inside the part, so matching never unifies against
  anything but a sort's head.

The viewer, `View.Arith.of`, converts the theory's **sort-erased** view: that has read the kind, the
kids and the indices, and the typed view adds what the sort adds — the sort fields, read off the
kids, and the proofs. It answers `none` where it cannot: a kid whose sort no `Typ` describes, a sort
that does not fit the operator.

- `gen_typed_view% from <Spec module>` generates and registers a theory's typed view.
- `register_typed_view% <View> [ctor KIND, …]` registers a hand-written one, whose constructors
  are the theory view's own.
- `def.typed_term_view V` — `def.term_view V` under `open Cvc.Typed` — generates the aggregate
  `V : Typ → Type`: the leaves, a variant `of<Theory>` per theory, `other`, one
  `@[match_pattern]` abbreviation per operator, a viewer `V.of`, and a `ViewFamily` instance.
-/

namespace Cvc.TypedView public meta section

open Lean Elab Command



/-! ## Emitted names

Built with `mkIdent` and spliced, never written in a quotation: a name written there resolves
against this module's environment, which imports neither layer.
-/

/-- `Cvc.Typed.View.reindex`. -/
def id_Cvc_Typed_View_reindex : Ident := mkIdent `Cvc.Typed.View.reindex
/-- `Cvc.Typed.View.kids`. -/
def id_Cvc_Typed_View_kids : Ident := mkIdent `Cvc.Typed.View.kids
/-- `Cvc.Typed.View.typOf?`. -/
def id_Cvc_Typed_View_typOfQ : Ident := mkIdent `Cvc.Typed.View.typOf?
/-- `Cvc.Typed.View.proof?`. -/
def id_Cvc_Typed_View_proofQ : Ident := mkIdent `Cvc.Typed.View.proof?
/-- `Cvc.Untyped.Kids.first`. -/
def id_Cvc_Untyped_Kids_first : Ident := mkIdent `Cvc.Untyped.Kids.first
/-- `Cvc.Typed.Term.erase`. -/
def id_Cvc_Typed_Term_erase : Ident := mkIdent `Cvc.Typed.Term.erase
/-- `Cvc.Bag`. -/
def id_Cvc_Bag : Ident := mkIdent `Cvc.Bag
/-- `Cvc.Env`. -/
def id_Cvc_Env : Ident := mkIdent `Cvc.Env
/-- `Cvc.FiniteField`. -/
def id_Cvc_FiniteField : Ident := mkIdent `Cvc.FiniteField
/-- `Cvc.Float`. -/
def id_Cvc_Float : Ident := mkIdent `Cvc.Float
/-- `Cvc.Set`. -/
def id_Cvc_Set : Ident := mkIdent `Cvc.Set
/-- `Cvc.ToTyp`. -/
def id_Cvc_ToTyp : Ident := mkIdent `Cvc.ToTyp
/-- `Cvc.TotalMap`. -/
def id_Cvc_TotalMap : Ident := mkIdent `Cvc.TotalMap
/-- `Cvc.Typ`. -/
def id_Cvc_Typ : Ident := mkIdent `Cvc.Typ
/-- `Cvc.Typ.Denote`. -/
def id_Cvc_Typ_Denote : Ident := mkIdent `Cvc.Typ.Denote
/-- `Cvc.Typ.arrayTo`. -/
def id_Cvc_Typ_arrayTo : Ident := mkIdent `Cvc.Typ.arrayTo
/-- `Cvc.Typ.bag`. -/
def id_Cvc_Typ_bag : Ident := mkIdent `Cvc.Typ.bag
/-- `Cvc.Typ.bitVec`. -/
def id_Cvc_Typ_bitVec : Ident := mkIdent `Cvc.Typ.bitVec
/-- `Cvc.Typ.finiteField`. -/
def id_Cvc_Typ_finiteField : Ident := mkIdent `Cvc.Typ.finiteField
/-- `Cvc.Typ.float`. -/
def id_Cvc_Typ_float : Ident := mkIdent `Cvc.Typ.float
/-- `Cvc.Typ.function`. -/
def id_Cvc_Typ_function : Ident := mkIdent `Cvc.Typ.function
/-- `Cvc.Typ.of`. -/
def id_Cvc_Typ_of : Ident := mkIdent `Cvc.Typ.of
/-- `Cvc.Typ.seq`. -/
def id_Cvc_Typ_seq : Ident := mkIdent `Cvc.Typ.seq
/-- `Cvc.Typ.set`. -/
def id_Cvc_Typ_set : Ident := mkIdent `Cvc.Typ.set
/-- `Cvc.Typ?.typ`. -/
def id_Cvc_TypQ_typ : Ident := mkIdent `Cvc.Typ?.typ
/-- `Cvc.Typed.BVar`. -/
def id_Cvc_Typed_BVar : Ident := mkIdent `Cvc.Typed.BVar
/-- `Cvc.Typed.Kids`. -/
def id_Cvc_Typed_Kids : Ident := mkIdent `Cvc.Typed.Kids
/-- `Cvc.Typed.Term`. -/
def id_Cvc_Typed_Term : Ident := mkIdent `Cvc.Typed.Term
/-- `Cvc.Typed.Term.asBVar`. -/
def id_Cvc_Typed_Term_asBVar : Ident := mkIdent `Cvc.Typed.Term.asBVar
/-- `Cvc.Typed.Term.getKind?`. -/
def id_Cvc_Typed_Term_getKindQ : Ident := mkIdent `Cvc.Typed.Term.getKind?
/-- `Cvc.Typed.Term.getSymbol`. -/
def id_Cvc_Typed_Term_getSymbol : Ident := mkIdent `Cvc.Typed.Term.getSymbol
/-- `cvc5.Kind.CONSTANT`. -/
def id_cvc5_Kind_CONSTANT : Ident := mkIdent `cvc5.Kind.CONSTANT
/-- `cvc5.Kind.VARIABLE`. -/
def id_cvc5_Kind_VARIABLE : Ident := mkIdent `cvc5.Kind.VARIABLE



/-- `Cvc.Typ.denoteWithOrd`. -/
def id_Cvc_Typ_denoteWithOrd : Ident := mkIdent `Cvc.Typ.denoteWithOrd
/-- `Cvc.Typed.ViewFamily`. -/
def id_Cvc_Typed_ViewFamily : Ident := mkIdent `Cvc.Typed.ViewFamily




/-! ## Sorts with a view -/

/-- A sort a part produces, or a wrapper views. -/
structure Head where
  /-- The head's name: `bool`, `bitVec`, `set`, …, or `any` for every sort. -/
  name : Name
  /-- The wrapper's name: `Bool`, `BitVec`, `Set`, …, `Any`. -/
  wrapper : String
  /-- The part's (and wrapper's) parameters. -/
  params : Array (TSyntax ``Parser.Term.bracketedBinder)
  /-- Those parameters as arguments, instances excluded. -/
  args : Array Term
  /-- Every parameter as an argument, a hole for each instance: what an `@`-application passes. -/
  allArgs : Array Term
  /-- The Lean type of the terms it views. -/
  target : Term
  /-- The kind of its values, which the wrapper's `.value` leaf reads. -/
  valueKind : Option Name
  /-- The parameters that carry an `Ord` instance. -/
  ordered : Array Name := #[]

/-- A head with no parameters. -/
def Head.plain (name : Name) (wrapper : String) (target : Name) (valueKind : Option Name) : Head :=
  ⟨name, wrapper, #[], #[], #[], mkIdent target, valueKind, #[]⟩

/-- A size parameter's binder. -/
def sizeParam (x : Ident) : MacroM (Array (TSyntax ``Parser.Term.bracketedBinder)) := do
  return #[← `(bracketedBinder| ($x : Nat))]

/-- A type parameter's binders: the type, its order if a container keys on it, and its sort. -/
def typeParam (x : Ident) (ord : Bool)
: MacroM (Array (TSyntax ``Parser.Term.bracketedBinder)) := do
  let ty ← `(bracketedBinder| ($x : Type))
  let toTyp ← `(bracketedBinder| [$id_Cvc_ToTyp $x])
  if ord then return #[ty, ← `(bracketedBinder| [Ord $x]), toTyp] else return #[ty, toTyp]

/-- The heads this prototype supports. Parameters are named apart from every specification's
variables, so that a result's own variable can be unified with one. -/
def headOf : Name → MacroM Head
  | `bool => return .plain `bool "Bool" `_root_.Bool (some `CONST_BOOLEAN)
  | `int => return .plain `int "Int" `_root_.Int (some `CONST_INTEGER)
  | `real => return .plain `real "Rat" `_root_.Rat (some `CONST_RATIONAL)
  | `string => return .plain `string "String" `_root_.String (some `CONST_STRING)
  | `regex => return .plain `regex "Regex" `Cvc.Regex none
  | `roundingMode =>
    return .plain `roundingMode "RoundingMode" `Cvc.Float.RoundingMode (some `CONST_ROUNDINGMODE)
  | `bitVec => do
    let w := mkIdent `w
    return ⟨`bitVec, "BitVec", ← sizeParam w, #[w], #[w], ← `(_root_.BitVec $w),
      some `CONST_BITVECTOR, #[]⟩
  | `float => do
    let (e, s) := (mkIdent `fe, mkIdent `fs)
    return ⟨`float, "Float", (← sizeParam e) ++ (← sizeParam s), #[e, s], #[e, s],
      ← `($id_Cvc_Float $e $s), some `CONST_FLOATINGPOINT, #[]⟩
  | `finiteField => do
    let q := mkIdent `q
    return ⟨`finiteField, "FiniteField", ← sizeParam q, #[q], #[q], ← `($id_Cvc_FiniteField $q),
      some `CONST_FINITE_FIELD, #[]⟩
  | `seq => do
    let γ := mkIdent `γ
    return ⟨`seq, "Seq", ← typeParam γ false, #[γ], #[γ, ← `(_)], ← `(_root_.Array $γ),
      some `CONST_SEQUENCE, #[]⟩
  | `set => do
    let γ := mkIdent `γ
    return ⟨`set, "Set", ← typeParam γ true, #[γ], #[γ, ← `(_), ← `(_)], ← `($id_Cvc_Set $γ), none,
      #[`γ]⟩
  | `bag => do
    let γ := mkIdent `γ
    return ⟨`bag, "Bag", ← typeParam γ true, #[γ], #[γ, ← `(_), ← `(_)], ← `($id_Cvc_Bag $γ), none,
      #[`γ]⟩
  | `array => do
    let (ξ, ζ) := (mkIdent `ξ, mkIdent `ζ)
    return ⟨`array, "TotalMap", (← typeParam ξ true) ++ (← typeParam ζ false), #[ξ, ζ],
      #[ξ, ← `(_), ← `(_), ζ, ← `(_)], ← `($id_Cvc_TotalMap $ξ $ζ), none, #[`ξ]⟩
  | `any => do
    let β := mkIdent `β
    return ⟨`any, "Any", ← typeParam β false, #[β], #[β, ← `(_)], β, none, #[]⟩
  | h => Macro.throwError s!"no view for sorts of head `{h}`"

/-- The same binders with every explicit one made implicit, for a function whose parameters are
determined by its argument's type. -/
def implicitBinders (bs : Array (TSyntax ``Parser.Term.bracketedBinder))
: MacroM (Array (TSyntax ``Parser.Term.bracketedBinder)) :=
  bs.mapM fun b => match b with
    | `(bracketedBinder| ($x : $ty)) => `(bracketedBinder| {$x : $ty})
    | _ => return ⟨b⟩

/-- The head of a result shape, if a part can be generated for it. -/
def shapeHead? : Shape → Option Name
  | .bool => some `bool
  | .int => some `int
  | .real => some `real
  | .string => some `string
  | .regex => some `regex
  | .roundingMode => some `roundingMode
  | .bitVec _ => some `bitVec
  | .float .. => some `float
  | .finiteField _ => some `finiteField
  | .seq _ => some `seq
  | .set _ => some `set
  | .bag _ => some `bag
  | .array .. => some `array
  | .var _ => some `any
  | .fn .. => none

/-- A component of a result that one of its head's parameters stands for. -/
inductive Comp where
  | size (e : SizeExpr)
  | type (s : Shape)

/-- What each of a head's parameters stands for in a result of that head, in parameter order. -/
def resultComps (args : Array Term) : Shape → Array (Comp × Term)
  | .bitVec e | .finiteField e => #[(.size e, args[0]!)]
  | .float e s => #[(.size e, args[0]!), (.size s, args[1]!)]
  | .seq x | .set x | .bag x => #[(.type x, args[0]!)]
  | .array i e => #[(.type i, args[0]!), (.type e, args[1]!)]
  | .var v => #[(.type (.var v), args[0]!)]
  | _ => #[]

/-- The `Typ` predicate a refinement class stands for. -/
def classPred? : Name → Option Name
  | `IsArith => some `Cvc.Typ.isArith
  | `HasConcat => some `Cvc.Typ.hasConcat
  | _ => none



/-! ## Rendering kids -/

/-- How each variable of an entry is bound in its constructor. -/
structure Roles where
  /-- Type variables that are `Typ` fields. -/
  typFields : Array Name
  /-- Size variables that are `Nat` fields, read off a kid's sort. -/
  sizeFields : Array Name
  /-- A result variable unified with the part's parameter, and the parameter. -/
  subst : Array (Name × Term)
  /-- The substituted variables whose parameter carries an `Ord` instance. -/
  ordered : Array Name := #[]

/-- Renders a size expression, `arity` excluded. -/
partial def renderSize (r : Roles) : SizeExpr → Except String Term
  | .lit n => return Syntax.mkNumLit (toString n)
  | .var n => return (r.subst.find? (·.1 == n)).map (·.2) |>.getD (mkIdent n)
  | .add a b => do
    let a ← renderSize r a; let b ← renderSize r b; return ⟨Unhygienic.run `($a + $b)⟩
  | .sub a b => do
    let a ← renderSize r a; let b ← renderSize r b; return ⟨Unhygienic.run `($a - $b)⟩
  | .mul a b => do
    let a ← renderSize r a; let b ← renderSize r b; return ⟨Unhygienic.run `($a * $b)⟩
  | .arity => throw "a size computed from the number of arguments"

/-- Renders a shape as a `Typ`, type variables being `Typ` fields or a parameter's `Typ.of`. -/
partial def renderTyp (r : Roles) : Shape → Except String Term
  | .var v =>
    match r.subst.find? (·.1 == v) with
    | some (_, β) => return ⟨Unhygienic.run `($id_Cvc_Typ_of $β)⟩
    | none => return mkIdent v
  | .bool => return mkIdent `Cvc.Typ.bool
  | .int => return mkIdent `Cvc.Typ.int
  | .real => return mkIdent `Cvc.Typ.real
  | .string => return mkIdent `Cvc.Typ.string
  | .regex => return mkIdent `Cvc.Typ.regex
  | .roundingMode => return mkIdent `Cvc.Typ.roundingMode
  | .bitVec w => do let w ← renderSize r w; return ⟨Unhygienic.run `($id_Cvc_Typ_bitVec $w)⟩
  | .float e s => do
    let e ← renderSize r e; let s ← renderSize r s
    return ⟨Unhygienic.run `($id_Cvc_Typ_float $e $s)⟩
  | .finiteField s => do
    let s ← renderSize r s; return ⟨Unhygienic.run `($id_Cvc_Typ_finiteField $s)⟩
  | .seq e => do
    let e ← renderTyp r e; return ⟨Unhygienic.run `($id_Cvc_Typ_seq ($id_Cvc_TypQ_typ $e))⟩
  | .set e => do
    let e ← renderTyp r e; return ⟨Unhygienic.run `($id_Cvc_Typ_set ($id_Cvc_TypQ_typ $e))⟩
  | .bag e => do
    let e ← renderTyp r e; return ⟨Unhygienic.run `($id_Cvc_Typ_bag ($id_Cvc_TypQ_typ $e))⟩
  | .array i e => do
    let i ← renderTyp r i; let e ← renderTyp r e
    return ⟨Unhygienic.run `($id_Cvc_Typ_arrayTo ($id_Cvc_TypQ_typ $i) ($id_Cvc_TypQ_typ $e))⟩
  | .fn d c => do
    let d ← renderTyp r d; let c ← renderTyp r c
    return ⟨Unhygienic.run `($id_Cvc_Typ_function $d ($id_Cvc_TypQ_typ $c))⟩

/-- Renders a shape with no `Typ` field in it as the Lean type it denotes. -/
partial def renderLean (r : Roles) : Shape → Except String Term
  | .var v =>
    match r.subst.find? (·.1 == v) with
    | some (_, β) => return β
    | none => throw s!"type variable `{v}` is neither a field nor the part's parameter"
  | .bool => return mkIdent `_root_.Bool
  | .int => return mkIdent `_root_.Int
  | .real => return mkIdent `_root_.Rat
  | .string => return mkIdent `_root_.String
  | .regex => return mkIdent `Cvc.Regex
  | .roundingMode => return mkIdent `Cvc.Float.RoundingMode
  | .bitVec w => do let w ← renderSize r w; return ⟨Unhygienic.run `(_root_.BitVec $w)⟩
  | .float e s => do
    let e ← renderSize r e; let s ← renderSize r s
    return ⟨Unhygienic.run `($id_Cvc_Float $e $s)⟩
  | .finiteField s => do let s ← renderSize r s; return ⟨Unhygienic.run `($id_Cvc_FiniteField $s)⟩
  | .seq e => do let e ← renderLean r e; return ⟨Unhygienic.run `(_root_.Array $e)⟩
  | .set e => do let e ← renderLean r e; return ⟨Unhygienic.run `($id_Cvc_Set $e)⟩
  | .bag e => do let e ← renderLean r e; return ⟨Unhygienic.run `($id_Cvc_Bag $e)⟩
  | .array i e => do
    let i ← renderLean r i; let e ← renderLean r e
    return ⟨Unhygienic.run `($id_Cvc_TotalMap $i $e)⟩
  | .fn d c => do
    let d ← renderLean r d; let c ← renderLean r c
    return ⟨Unhygienic.run `($d → $c)⟩

/-- The index of a kid of this shape: the denotation of its `Typ` if a `Typ` field occurs in it,
which reduces once the field is matched, and the Lean type it denotes otherwise. -/
def renderKid (r : Roles) (shape : Shape) : Except String Term := do
  -- a container keyed on a parameter that carries no order cannot be spelled as a Lean type either
  let unordered := shape.ordVars.any fun v => r.subst.any (·.1 == v) && !r.ordered.contains v
  if shape.typeVars.any r.typFields.contains || unordered then
    let typ ← renderTyp r shape
    return ⟨Unhygienic.run `($id_Cvc_Typ_Denote $typ)⟩
  else renderLean r shape

/-- A pattern on a kid's `Typ` binding `target` where the shape mentions it, or `none` if it is not
at a position a pattern can reach. -/
partial def bindIn (target : Name) (isSize : Bool) : Shape → Option Term
  | .var v => if !isSize && v == target then some (mkIdent target) else none
  | .bitVec (.var n) =>
    if isSize && n == target then some ⟨Unhygienic.run `($id_Cvc_Typ_bitVec $(mkIdent target))⟩
    else none
  | .finiteField (.var n) =>
    if isSize && n == target then some ⟨Unhygienic.run `($id_Cvc_Typ_finiteField $(mkIdent target))⟩
    else none
  | .float e s =>
    let x := mkIdent target
    match isSize, e, s with
    | true, .var n, _ => if n == target then some ⟨Unhygienic.run `($id_Cvc_Typ_float $x _)⟩ else
      match s with
      | .var m => if m == target then some ⟨Unhygienic.run `($id_Cvc_Typ_float _ $x)⟩ else none
      | _ => none
    | true, _, .var m =>
      if m == target then some ⟨Unhygienic.run `($id_Cvc_Typ_float _ $x)⟩ else none
    | _, _, _ => none
  | .seq e => (bindIn target isSize e).map fun p =>
    ⟨Unhygienic.run `($id_Cvc_Typ_seq ($id_Cvc_TypQ_typ $p))⟩
  | .set e => (bindIn target isSize e).map fun p =>
    ⟨Unhygienic.run `($id_Cvc_Typ_set ($id_Cvc_TypQ_typ $p))⟩
  | .bag e => (bindIn target isSize e).map fun p =>
    ⟨Unhygienic.run `($id_Cvc_Typ_bag ($id_Cvc_TypQ_typ $p))⟩
  | .array i e =>
    match bindIn target isSize i with
    | some p => some ⟨Unhygienic.run `($id_Cvc_Typ_arrayTo ($id_Cvc_TypQ_typ $p) _)⟩
    | none => (bindIn target isSize e).map fun p =>
      ⟨Unhygienic.run `($id_Cvc_Typ_arrayTo _ ($id_Cvc_TypQ_typ $p))⟩
  | .fn d c =>
    match bindIn target isSize d with
    | some p => some ⟨Unhygienic.run `($id_Cvc_Typ_function $p _)⟩
    | none => (bindIn target isSize c).map fun p =>
      ⟨Unhygienic.run `($id_Cvc_Typ_function _ ($id_Cvc_TypQ_typ $p))⟩
  | _ => none






/-! ## The theory views' heads -/

/-- How a part's head appears in the sort-indexed view. -/
structure AtHead where
  /-- The theory constructor's fields ahead of the part. -/
  fields : Array (TSyntax ``Parser.Term.bracketedBinder)
  /-- The arguments for those fields. -/
  fieldArgs : Array Term
  /-- The part's parameters, as named arguments. -/
  partArgs : Array (TSyntax ``Parser.Term.namedArgument)
  /-- The sort the theory constructor is indexed by. -/
  index : Term
  /-- A pattern on a node's sort matching the head, binding the fields. -/
  pattern : Term
  /-- The abbreviations' binders standing for the fields. -/
  implicits : Array (TSyntax ``Parser.Term.bracketedBinder)
  /-- The field whose denotation must be ordered, for the containers keyed on it. -/
  ordered : Option Ident := none

/-- A part's head in the sort-indexed view. -/
def atHead : Name → MacroM AtHead
  | `any => do
    let τ := mkIdent `τ
    return { fields := #[], fieldArgs := #[], index := τ, pattern := τ
             partArgs := #[← `(Parser.Term.namedArgument| ($(mkIdent `β) := $id_Cvc_Typ_Denote $τ))]
             implicits := #[← `(bracketedBinder| {$τ : $id_Cvc_Typ})] }
  | `bitVec => sizes `bitVec #[`w]
  | `float => sizes `float #[`fe, `fs]
  | `finiteField => sizes `finiteField #[`q]
  | `seq => types `seq #[`γ] none
  | `set => types `set #[`γ] (some `γ)
  | `bag => types `bag #[`γ] (some `γ)
  | `array => types `arrayTo #[`ξ, `ζ] (some `ξ)
  | h => do
    let ctor := mkIdent (`Cvc.Typ ++ h)
    return { fields := #[], fieldArgs := #[], partArgs := #[], index := ctor, pattern := ctor
             implicits := #[] }
where
  sizes (ctor : Name) (names : Array Name) : MacroM AtHead := do
    let xs := names.map mkIdent
    let c := mkIdent (`Cvc.Typ ++ ctor)
    let index ← `($c $xs*)
    return { fields := ← xs.mapM fun x => `(bracketedBinder| ($x : Nat)), fieldArgs := xs
             partArgs := ← xs.mapM fun x => `(Parser.Term.namedArgument| ($x := $x))
             index, pattern := index
             implicits := ← xs.mapM fun x => `(bracketedBinder| {$x : Nat}) }
  types (ctor : Name) (names : Array Name) (ord : Option Name) : MacroM AtHead := do
    let xs := names.map mkIdent
    let c := mkIdent (`Cvc.Typ ++ ctor)
    let wrapped ← xs.mapM fun x => `($id_Cvc_TypQ_typ $x)
    let index ← `($c $wrapped*)
    let mut fields ← xs.mapM fun x => `(bracketedBinder| ($x : $id_Cvc_Typ))
    let mut implicits ← xs.mapM fun x => `(bracketedBinder| {$x : $id_Cvc_Typ})
    if let some o := ord then
      let ordTy ← `(Ord ($id_Cvc_Typ_Denote $(mkIdent o)))
      fields := fields.push (← `(bracketedBinder| [$ordTy]))
      -- named, not instance-implicit: a pattern binds it, where it could not synthesize it, and a
      -- local of class type is an instance in the body all the same
      implicits := implicits.push (← `(bracketedBinder| {$(mkIdent `ord) : $ordTy}))
    return { fields, fieldArgs := xs, index, pattern := index, implicits
             partArgs := ← xs.mapM fun x =>
               `(Parser.Term.namedArgument| ($x := $id_Cvc_Typ_Denote $x))
             ordered := ord.map mkIdent }



/-! ## The registry -/

/-- A typed view's constructor, as the aggregate's abbreviations need it. -/
structure TypedCtor where
  /-- The operator's name, which its abbreviation takes. -/
  name : Name
  /-- For a generated view, the part holding the operator and the part's head; `none` for a
  hand-written view, whose constructors are the theory view's own. -/
  part : Option (Name × Name) := none
deriving Inhabited

/-- A registered typed view. -/
structure TypedViewEntry where
  /-- The theory, `Arith`. -/
  theory : Name
  /-- The theory view, `Cvc.Typed.View.Arith`. -/
  view : Name
  /-- Its operators. -/
  ctors : Array TypedCtor
  /-- The kinds it takes apart. -/
  kinds : Array Name
deriving Inhabited

/-- The registered typed views, imported ones included. -/
initialize typedViewExt : SimplePersistentEnvExtension TypedViewEntry (Array TypedViewEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun ess => ess.foldl (· ++ ·) #[]
  }

/-- Every registered typed view. -/
def typedViews [Monad m] [MonadEnv m] : m (Array TypedViewEntry) :=
  return typedViewExt.getState (← getEnv)



/-! ## A theory's typed view -/

/-- One entry's constructor in its part, and the theory viewer's alternative for it. -/
structure GenCtor where
  ctor : TSyntax ``Parser.Command.ctor
  alt : TSyntax ``Parser.Term.matchAlt

/-- Whether an entry's kids are an n-ary array: an n-ary entry over two arguments of one shape. -/
def naryKids (spec : OpSpec) : Bool :=
  !(spec.nary matches .never) && spec.args.size == 2 && spec.args[0]!.shape == spec.args[1]!.shape

/-- Generates an entry's constructor in its part, and the alternative converting its sort-erased
constructor — or why it cannot be. `theory` names the theory view, `untyped` the sort-erased one.
-/
def genCtor (spec : OpSpec) (theory untyped part : Name) (head : Head)
: MacroM (Except String GenCtor) := do
  let fail (why : String) : MacroM (Except String GenCtor) := return .error why
  -- exactly what the sort-erased view has no constructor for, there being nothing to convert
  if viewValueKinds.contains spec.kind then return ← fail "a value, the `.value` leaf"
  if spec.kind == `CONSTANT then return ← fail "a declared symbol, the `.symbol` leaf"
  if spec.tmFn.isSome && !(spec.args.isEmpty && spec.valArgs.isEmpty && spec.indices.isEmpty) then
    return ← fail "a `tm` constructor taking arguments"
  if !spec.valArgs.isEmpty then return ← fail "takes Lean values"
  -- what the result fixes: a variable becomes the part's parameter, anything else an equation
  -- between the parameter and what the result computes — a size's, or a sort's over `Typ`
  let mut subst : Array (Name × Term) := #[]
  let mut sizeEqs : Array (SizeExpr × Term) := #[]
  let mut typeEqs : Array (Shape × Term) := #[]
  for (comp, param) in resultComps head.args spec.ret do
    match comp with
    | .size (.var n) =>
      if spec.sizeVars.contains n && !subst.any (·.1 == n) then subst := subst.push (n, param)
      else sizeEqs := sizeEqs.push (.var n, param)
    | .size e => sizeEqs := sizeEqs.push (e, param)
    | .type (.var α) =>
      if spec.tyVars.any (·.name == α) && !subst.any (·.1 == α) then subst := subst.push (α, param)
      else typeEqs := typeEqs.push (.var α, param)
    | .type x => typeEqs := typeEqs.push (x, param)
  let substituted := subst.map (·.1)
  let roles : Roles := {
    typFields := spec.tyVars.map (·.name) |>.filter (!substituted.contains ·)
    sizeFields := spec.sizeVars.filter (!substituted.contains ·)
    subst
    ordered := subst.filterMap fun (v, p) =>
      if head.ordered.contains p.raw.getId then some v else none
  }
  let nary := naryKids spec
  -- the sort-erased constructor's fields, bound by the alternative's pattern
  let idxIds := spec.indices.map mkIdent
  let kidIds := if nary then #[mkIdent `kids] else spec.args.map (mkIdent ·.name)
  let kidTerm (i : Nat) : MacroM Term :=
    if nary then `($id_Cvc_Untyped_Kids_first $(kidIds[0]!)) else return kidIds[i]!
  -- fields, and the alternative's code computing each
  let mut binders : Array (TSyntax ``Parser.Term.bracketedBinder) := #[]
  let mut fieldArgs : Array Term := #[]
  -- each step wraps what follows it, answering `none` where it cannot go on
  let mut steps : Array (Term → MacroM Term) := #[]
  for i in idxIds do
    binders := binders.push (← `(bracketedBinder| ($i : Nat)))
    fieldArgs := fieldArgs.push i
  -- a free variable is read off the first kid whose sort mentions it where a pattern reaches; a
  -- kid with no `Typ`, or of an unexpected sort, makes the whole view `none`
  let readVar (v : Name) (isSize : Bool) : MacroM (Option (Term → MacroM Term)) := do
    for (arg, i) in spec.args.zipIdx do
      if let some pat := bindIn v isSize arg.shape then
        let kid ← kidTerm (if nary then 0 else i)
        return some fun rest => `(do
          let sort? ← ($id_Cvc_Typed_View_typOfQ $kid)
          match sort? with
          | some $pat:term => $rest:term
          | _ => return none)
    return none
  for n in roles.sizeFields do
    let some step ← readVar n true | return ← fail s!"size `{n}` is not readable off an operand"
    binders := binders.push (← `(bracketedBinder| ($(mkIdent n) : Nat)))
    fieldArgs := fieldArgs.push (mkIdent n)
    steps := steps.push step
  for α in roles.typFields do
    let some step ← readVar α false | return ← fail s!"type `{α}` is not readable off an operand"
    binders := binders.push (← `(bracketedBinder| ($(mkIdent α) : $id_Cvc_Typ)))
    fieldArgs := fieldArgs.push (mkIdent α)
    steps := steps.push step
  -- implicit proofs: a field's classes, the parameter's, and a computed result's equation. Each is
  -- stated twice: over the part's parameters for its binder, and over what they are in the
  -- conversion — where the sort-erased term's sort was matched, a type parameter being the
  -- denotation of a `Typ` the pattern bound
  let altParam (p : Term) : MacroM Term := do
    let n := p.raw.getId
    if n == `β then `($id_Cvc_Typ_Denote $(mkIdent `τ'))
    else if [`γ, `ξ, `ζ].contains n then `($id_Cvc_Typ_Denote $(mkIdent n))
    else return p
  let rolesAlt := { roles with subst := ← roles.subst.mapM fun (v, p) => return (v, ← altParam p) }
  let mut proofs : Array (Term × Term) := #[]
  for tv in spec.tyVars do
    for cls in tv.classes do
      let some pred := classPred? cls | return ← fail s!"class `{cls}` has no `Typ` predicate"
      let (subject, subjectAlt) ← match subst.find? (·.1 == tv.name) with
        | some (_, β) => do pure (← `($id_Cvc_Typ_of $β), ← `($id_Cvc_Typ_of $(← altParam β)))
        | none => pure (mkIdent tv.name, mkIdent tv.name)
      proofs := proofs.push
        (← `($(mkIdent pred) $subject = true), ← `($(mkIdent pred) $subjectAlt = true))
  for (e, w) in sizeEqs do
    match renderSize roles e, renderSize rolesAlt e with
    | .ok e, .ok eAlt => proofs := proofs.push (← `($e = $w), ← `($eAlt = $(← altParam w)))
    | .error why, _ | _, .error why => return ← fail why
  for (x, γ) in typeEqs do
    match renderTyp roles x, renderTyp rolesAlt x with
    | .ok x, .ok xAlt =>
      proofs := proofs.push
        (← `($id_Cvc_Typ_of $γ = $x), ← `($id_Cvc_Typ_of $(← altParam γ) = $xAlt))
    | .error why, _ | _, .error why => return ← fail why
  for ((prop, propAlt), i) in proofs.zipIdx do
    let h := mkIdent (Name.mkSimple s!"h{i}")
    binders := binders.push (← `(bracketedBinder| {$h : $prop}))
    fieldArgs := fieldArgs.push h
    steps := steps.push fun rest => `(match ($id_Cvc_Typed_View_proofQ ($propAlt)) with
      | some ⟨$h⟩ => $rest
      | none => return none)
  -- the kids, typed
  let mut kidArgs : Array Term := #[]
  if nary then
    let some arg := spec.args[0]? | return ← fail "no argument"
    let ty ← match renderKid roles arg.shape with
      | .ok ty => pure ty
      | .error why => return ← fail why
    binders := binders.push (← `(bracketedBinder| ($(mkIdent `kids) : $id_Cvc_Typed_Kids $ty)))
    kidArgs := kidArgs.push (← `($id_Cvc_Typed_View_kids $(kidIds[0]!)))
  else
    for (arg, k) in spec.args.zip kidIds do
      let ty ← match renderKid roles arg.shape with
        | .ok ty => pure ty
        | .error why => return ← fail why
      binders := binders.push (← `(bracketedBinder| ($(mkIdent arg.name) : $id_Cvc_Typed_Term $ty)))
      kidArgs := kidArgs.push (← `($id_Cvc_Typed_View_reindex $k))
  let ctor ← `(Parser.Command.ctor|
    $(viewDoc spec.doc):docComment | $(mkIdent spec.id):ident $binders*)
  -- the alternative: the sort's head and the sort-erased constructor, then the conversion
  let at_ ← atHead head.name
  let holes : Array Term ← (List.replicate (1 + head.params.size) 0).toArray.mapM fun _ => `(_)
  let partApp ← `(@$(mkIdent (part ++ spec.id)) $holes* $fieldArgs* $kidArgs*)
  let tauP := mkIdent `τ'
  let thApp ← if head.name == `any then
      `($(mkIdent (theory ++ `any)) ($(mkIdent `τ) := $tauP) $partApp)
    else `($(mkIdent (theory ++ head.name)) $(at_.fieldArgs)* $partApp)
  let mut body ← `(return some $thApp)
  for step in steps.reverse do
    body ← step body
  if let some o := at_.ordered then
    body ← `(match ($id_Cvc_Typ_denoteWithOrd $o).2 with
      | some inst => letI : Ord ($id_Cvc_Typ_Denote $o) := inst; $body
      | none => return none)
  let sortPat : Term := if head.name == `any then tauP else at_.pattern
  let untypedPat ← `($(mkIdent (untyped ++ spec.id)) $idxIds* $kidIds*)
  let alt ← `(Parser.Term.matchAltExpr| | $sortPat, some $untypedPat => $body)
  return .ok { ctor, alt }

/-- A part's name: `Cvc.Typed.View.Arith.OnBool`. -/
def partName (theory : Name) (head : Head) : Name := theory ++ Name.mkSimple s!"On{head.wrapper}"

/-- Generates and registers a theory's typed view from its specification module. -/
syntax (name := genTypedViewStx) "gen_typed_view% " "from " ident : command

@[command_elab genTypedViewStx]
def elabGenTypedView : CommandElab
  | `(gen_typed_view% from $mod:ident) => do
    let specs ← opSpecsOf mod.getId
    if specs.isEmpty then throwErrorAt mod s!"`{mod.getId}` declares no operator specification"
    let theoryName := mod.getId.components.getLast!
    let theory := `Cvc.Typed.View ++ theoryName
    let untyped := `Cvc.Untyped.View ++ theoryName
    -- the parts, by the head of each entry's result, in specification order
    let mut heads : Array Name := #[]
    for spec in specs do
      if let some h := shapeHead? spec.ret then
        unless heads.contains h do heads := heads.push h
    let mut thCtors := #[]
    let mut alts : Array (TSyntax ``Parser.Term.matchAlt) := #[]
    let mut ctors : Array TypedCtor := #[]
    let mut kinds : Array Name := #[]
    for h in heads do
      let head ← liftMacroM (headOf h)
      let part := partName theory head
      let mut partCtors := #[]
      for spec in specs do
        unless shapeHead? spec.ret == some h do continue
        if kinds.contains spec.kind then continue
        if let .ok gen ← liftMacroM (genCtor spec theory untyped part head) then
          partCtors := partCtors.push gen.ctor
          alts := alts.push gen.alt
          ctors := ctors.push { name := spec.id, part := some (part, h) }
          kinds := kinds.push spec.kind
      if partCtors.isEmpty then continue
      let doc := viewDoc s!"`{theoryName}`'s operators producing {head.wrapper}."
      elabCommand (← `($doc:docComment
        inductive $(mkIdent (`_root_ ++ part)) $(head.params)* where $partCtors*))
      let at_ ← liftMacroM (atHead h)
      let partTy := Syntax.mkApp (mkIdent part) (at_.partArgs.map (⟨·.raw⟩))
      let implicitTau ← if h == `any then
          pure #[← `(bracketedBinder| {$(mkIdent `τ) : $id_Cvc_Typ})]
        else pure #[]
      thCtors := thCtors.push (← `(Parser.Command.ctor|
        | $(mkIdent h):ident $implicitTau* $(at_.fields)* (v : $partTy)
          : $(mkIdent theory) $(at_.index)))
    if thCtors.isEmpty then return
    let doc := viewDoc
      s!"`{theoryName}`'s operators, taken apart one level, indexed by the sort each produces."
    elabCommand (← `($doc:docComment
      protected inductive $(mkIdent (`_root_ ++ theory)) : $id_Cvc_Typ → Type where $thCtors*))
    let tau := mkIdent `τ
    let t := mkIdent `t
    let ofDoc := viewDoc s!"Takes a term apart one level, at its sort, if `{theoryName}` owns its \
      operator and the term's sort fits it."
    elabCommand (← `(
      $ofDoc:docComment
      def $(mkIdent (`_root_ ++ theory ++ `of)) ($tau:ident : $id_Cvc_Typ)
        ($t : $id_Cvc_Typed_Term ($id_Cvc_Typ_Denote $tau))
      : $id_Cvc_Env (Option ($(mkIdent theory) $tau)) :=
        match $tau:term, ($(mkIdent (untyped ++ `of?)) ($id_Cvc_Typed_Term_erase $t)) with
        $[$alts:matchAlt]*
        | _, _ => return none))
    modifyEnv (typedViewExt.addEntry · { theory := theoryName, view := theory, ctors, kinds })
  | _ => throwUnsupportedSyntax

/-- Registers a hand-written typed view: its theory view, whose constructors are the operators,
and each with the kind it owns. The theory is the view's last component. -/
syntax (name := registerTypedViewStx)
  "register_typed_view% " ident "[" (ident ident),* "]" : command

@[command_elab registerTypedViewStx]
def elabRegisterTypedView : CommandElab
  | `(register_typed_view% $view [$[$cs $ks],*]) => do
    let view ← liftCoreM (realizeGlobalConstNoOverload view)
    let entry := { theory := view.components.getLast!, view
                   ctors := cs.map ({ name := ·.getId }), kinds := ks.map (·.getId) }
    modifyEnv (typedViewExt.addEntry · entry)
  | _ => throwUnsupportedSyntax



/-! ## The typed aggregate -/

/-- Generates the typed aggregate `V : Typ → Type` from every registered typed view. -/
syntax (name := typedTermViewStx) "def.typed_term_view " ident : command

@[command_elab typedTermViewStx]
def elabTypedTermView : CommandElab
  | `(def.typed_term_view $v:ident) => do
    let views ← typedViews
    let agg := v.getId
    let aggId := mkIdent agg
    let leaves := #[`value, `symbol, `bvar, `other, `of, `instViewFamily]
    -- a kind is routed to one theory, and an abbreviation names one operator
    let mut owners : Array (Name × Name) := #[]
    let mut names : Array (Name × Name) :=
      leaves.map (·, agg) ++ views.map (theoryVariant ·.theory, agg)
    for vw in views do
      for k in vw.kinds do
        if let some (_, other) := owners.find? (·.1 == k) then
          throwError m!"`{agg}`: kind `{k}` is owned by both `{other}` and `{vw.view}`"
        owners := owners.push (k, vw.view)
      for c in vw.ctors do
        if let some (_, other) := names.find? (·.1 == c.name) then
          throwError m!"`{agg}`: `{c.name}` names an operator of `{vw.view}` and something of \
            `{other}`"
        names := names.push (c.name, vw.view)
    -- the aggregate
    let tau := mkIdent `τ
    let term ← `($id_Cvc_Typed_Term ($id_Cvc_Typ_Denote $tau))
    let mut variants := #[
      ← `(Parser.Command.ctor|
        | $(mkIdent `value):ident {$tau : $id_Cvc_Typ} (t : $term) : $aggId $tau),
      ← `(Parser.Command.ctor|
        | $(mkIdent `symbol):ident {$tau : $id_Cvc_Typ} (name : _root_.String) : $aggId $tau),
      ← `(Parser.Command.ctor|
        | $(mkIdent `bvar):ident {$tau : $id_Cvc_Typ}
            (x : $id_Cvc_Typed_BVar ($id_Cvc_Typ_Denote $tau)) : $aggId $tau)]
    for vw in views do
      variants := variants.push (← `(Parser.Command.ctor|
        | $(mkIdent (theoryVariant vw.theory)):ident {$tau : $id_Cvc_Typ}
            (v : $(mkIdent vw.view) $tau) : $aggId $tau))
    variants := variants.push (← `(Parser.Command.ctor|
      | $(mkIdent `other):ident {$tau : $id_Cvc_Typ} (t : $term) : $aggId $tau))
    let doc := viewDoc "A term of any sort, taken apart one level."
    elabCommand (← `($doc:docComment inductive $aggId : $id_Cvc_Typ → Type where $variants*))
    -- one abbreviation per operator, its binders read off its constructor
    for vw in views do
      let variant := mkIdent (agg ++ theoryVariant vw.theory)
      for c in vw.ctors do
        let ctorName := match c.part with
          | some (part, _) => part ++ c.name
          | none => vw.view ++ c.name
        -- a part's parameters are given by its head; a direct constructor's are bound implicitly,
        -- Lean promoting an index every constructor leaves uniform (`View.Apply`'s) to one
        let direct := c.part.isNone
        let fields ← liftTermElabM do
          let info ← getConstInfoCtor ctorName
          Meta.forallTelescope info.type fun xs _ => do
            let mut fields := #[]
            for x in xs, i in [0:xs.size] do
              let d ← x.fvarId!.getDecl
              if i < info.numParams then
                if direct && !d.binderInfo.isInstImplicit then
                  fields := fields.push (d.userName, BinderInfo.implicit)
              else fields := fields.push (d.userName, d.binderInfo)
            return fields
        let binders ← fields.mapM fun (n, bi) =>
          if bi.isExplicit then `(bracketedBinder| ($(mkIdent n) : _))
          else `(bracketedBinder| {$(mkIdent n) : _})
        let named ← fields.mapM fun (n, _) =>
          `(Parser.Term.namedArgument| ($(mkIdent n) := $(mkIdent n)))
        -- named arguments mix with positional ones only in an `app` node built directly
        let (implicits, inner) ← match c.part with
          | some (_, h) => do
            let at_ ← liftMacroM (atHead h)
            let partApp := Syntax.mkApp (mkIdent ctorName) ((at_.partArgs ++ named).map (⟨·.raw⟩))
            let tauArg ← if h == `any then
                pure #[⟨(← `(Parser.Term.namedArgument| ($tau := $tau))).raw⟩]
              else pure #[]
            let thApp :=
              Syntax.mkApp (mkIdent (vw.view ++ h)) (tauArg ++ at_.fieldArgs ++ #[partApp])
            pure (at_.implicits, thApp)
          | none => pure (#[], Syntax.mkApp (mkIdent ctorName) (named.map (⟨·.raw⟩)))
        -- no result type: with one, the binders' holes would be resolved before the body is seen
        elabCommand (← `(
          @[match_pattern] abbrev $(mkIdent (agg ++ c.name)) $implicits* $binders* :=
            $variant $inner))
    -- the viewer: the kind, routed to its theory
    let t := mkIdent `t
    let other := mkIdent (agg ++ `other)
    let mut alts : Array (TSyntax ``Parser.Term.matchAlt) := #[]
    for k in viewValueKinds do
      alts := alts.push (← `(Parser.Term.matchAltExpr|
        | some $(viewKindId k) => return $(mkIdent (agg ++ `value)) $t))
    alts := alts.push (← `(Parser.Term.matchAltExpr|
      | some $(viewKindId `CONSTANT) =>
        match ($id_Cvc_Typed_Term_getSymbol $t) with
        | .ok name => return $(mkIdent (agg ++ `symbol)) name
        | .error _ => return $other $t))
    alts := alts.push (← `(Parser.Term.matchAltExpr|
      | some $(viewKindId `VARIABLE) =>
        return $(mkIdent (agg ++ `bvar)) ($id_Cvc_Typed_Term_asBVar $t)))
    for vw in views do
      let variant := mkIdent (agg ++ theoryVariant vw.theory)
      for k in vw.kinds do
        alts := alts.push (← `(Parser.Term.matchAltExpr|
          | some $(viewKindId k) => do
            match ← ($(mkIdent (vw.view ++ `of)) $tau $t) with
            | some v => return $variant v
            | none => return $other $t))
    alts := alts.push (← `(Parser.Term.matchAltExpr| | _ => return $other $t))
    let ofDoc := viewDoc "Takes a term apart one level, at its sort."
    elabCommand (← `(
      $ofDoc:docComment
      def $(mkIdent (agg ++ `of)) ($tau:ident : $id_Cvc_Typ)
        ($t : $id_Cvc_Typed_Term ($id_Cvc_Typ_Denote $tau))
      : $id_Cvc_Env ($aggId $tau) :=
        match ($id_Cvc_Typed_Term_getKindQ $t) with $[$alts:matchAlt]*))
    elabCommand (← `(
      instance $(mkIdent (agg ++ `instViewFamily)):ident : $id_Cvc_Typed_ViewFamily $aggId :=
        ⟨$(mkIdent (agg ++ `of))⟩))
  | _ => throwUnsupportedSyntax

end

end Cvc.TypedView

namespace Cvc.Typed

/-- Generates the typed view `V` of every imported theory, `def.typed_term_view` under
`open Cvc.Typed`; see `Cvc.Gen.TypedView`. -/
scoped syntax "def.term_view " ident : command

macro_rules
  | `(def.term_view $v) => `(def.typed_term_view $v)

end Cvc.Typed
