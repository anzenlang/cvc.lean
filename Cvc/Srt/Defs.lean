/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Init.Data.Nat.Power2

import Cvc.Basic



namespace Cvc

open cvc5 renaming TermManager → Tm


open Lean.Parser.Command (ctor)

local syntax
  declModifiers
  withPosition("Cvc.mkSrt!" declId ", " declId ppLine
    (
      colGt (docComment)? ppLine
      colGt "| " ident "[" ident "]" optDeclSig
      -- colGt ctor -- " ← " ident
    )*
  )
: command

open Lean Elab Command in
elab_rules : command
| `(
  $mods:declModifiers
  Cvc.mkSrt! $Srt:ident, $Kind:ident $[
    $[ $doc?:docComment ]?
    | $variantId:ident [ $variantSortId:ident ] $variantSig:optDeclSig
  ]*
) => do
  let variantId' := variantId
  let variantStr := variantId.map fun v => Id.run do
    let mut s := toString v
    if let some s' := s.dropPrefix? "`" then
      s := s'.toString
    Lean.Syntax.mkStrLit s
  let identOfString := Lean.mkIdent ∘ Lean.Name.mkSimple
  let kindId := identOfString "kind"
  let ofSrtId := identOfString "ofSrt"
  -- let ofSortId := identOfString "ofSort"
  let toSortId := identOfString "toSort"
  let toStringId := identOfString "toString"
  let kind_ToStringId :=
    Lean.Name.mkStr2 Kind.getId.toString "toString"
    |> Lean.mkIdent
  let ToStringId ← ``(ToString)
  let cvc5SortKindId ← ``(cvc5.SortKind)
  -- let ResId ← ``(Res)
  -- let errorResId ← ``(Res.error)
  -- let internalErrorId ← ``(Error.internal)

  -- `Srt.Kind`
  elabCommand <| ← `(
    namespace $Srt
    /-- A sort kind. -/
    inductive $Kind:declId $[ | $variantId:ident ]*
    deriving Inhabited, Hashable, DecidableEq, Ord
    end $Srt
  )

  -- `Srt`
  elabCommand <| ← `(
    $mods:declModifiers
    inductive $Srt:declId $[
      $[ $doc?:docComment ]?
      | $variantId:ident $variantSig:optDeclSig
    ]*
    deriving Inhabited, Hashable
  )

  -- helpers
  elabCommand <| ← `(
    namespace $Srt
    /-- Turns a sort into a sort kind. -/
    def $kindId:declId : $Srt → $Kind $[ | .$variantId .. => .$variantId' ]*

    namespace $Kind
    @[inherit_doc $kindId]
    def $ofSrtId:declId := $kindId

    -- /-- Constructor from an unsafe sort. -/
    -- def $ofSortId:declId (sort : $cvc5SortKindId) : $ResId $Kind :=
    --   aux sort |>.context ls!"failed to convert unsafe sort `{sort}` to `Cvc.Srt.Kind`"
    -- where aux : $cvc5SortKindId → $ResId $Kind
    --   $[ | .$variantSortId:ident => return .$variantId ]*
    --   | k => $errorResId ($internalErrorId s!"unexpected unsafe sort kind `{k}`")

    /-- Turns itself into an unsafe sort. -/
    def $toSortId:declId : $Kind → $cvc5SortKindId
    $[ | .$variantId => .$variantSortId ]*

    /-- String representation. -/
    protected
    def $toStringId : $Kind:term → String $[ | .$variantId => $variantStr:str ]*

    instance : $ToStringId $Kind := ⟨$kind_ToStringId:term⟩
    end $Kind
    end $Srt
  )

/-- A cvc sort, `Sort`-coercion realized by `Srt.toType`. -/
Cvc.mkSrt! Srt, Kind
  /-- An abstract sort. -/
  | abstract[ABSTRACT_SORT] : (kind : Srt.Kind) → Srt

  /-- Total map from an *index* sort to an *element* sort.

  Called *array* in SMT-LIB/cvc.
  -/
  | array[ARRAY_SORT] : (idx elm : Srt) → Srt

  /-- A multi-set/bag of elements. -/
  | bag[BAG_SORT] : (elm : Srt) → Srt

  /-- Boolean sort. -/
  | bool[BOOLEAN_SORT] : Srt

  /-- Sort of bit-vectors of length `size`. -/
  | bitVec[BITVECTOR_SORT] : (size : Nat) → Srt

  -- /-- Datatype sort. -/
  -- | datatype[DATATYPE_SORT] : (args : Array Srt) → Srt

  /-- Finite field sort. -/
  | finiteField[FINITE_FIELD_SORT] : (size : Nat) → Srt

  /-- Floating-point sort. -/
  | float[FLOATINGPOINT_SORT] : (exp sig : UInt32) → Srt

  /-- Function sort.

  Cvc5 actually takes an array of domains, and I think, does not allow the codomain to be a function
  sort. We're trying to adapt cvc5 sorts for a lean world by pretending they behave as lean function
  types.
  -/
  | function[FUNCTION_SORT] : (dom : Srt) → (cod : Srt) → Srt
  /-- Integer sort. -/
  | int[INTEGER_SORT]
  /-- Product sort.

  Cvc5 has a notion of *tuple* or arity `[0, ∞[`, but that maps terribly to lean types. The goal
  with this constructor is to limit `Srt` creation to only (binary) products.
  -/
  | prod[TUPLE_SORT] : (lft rgt : Srt) → Srt
  /-- Real sort. -/
  | real[REAL_SORT]
  /-- Regular expression sort. -/
  | regex[REGLAN_SORT]
  /-- Rounding mode sort. -/
  | roundingMode[ROUNDINGMODE_SORT]
  /-- Array sort, called *sequence* in SMT-LIB/cvc. -/
  | seq[SEQUENCE_SORT] : (elm : Srt) → Srt
  /-- Set sort. -/
  | set[SET_SORT] : (elm : Srt) → Srt
  /-- String sort. -/
  | string[STRING_SORT]
  /-- Unit sort. -/
  | unit[TUPLE_SORT]
  /-- An uninterpreted sort. -/
  | uninterpreted[UNINTERPRETED_SORT] : (name : String) → Srt

namespace Srt

/-! # `DecidableEq` instance -/
mutual

instance instDecidableEqListSrt : DecidableEq (List Srt)
| hd1::tl1, hd2::tl2 => by
  cases hd1.instDecidableEq hd2
  case isFalse h => exact isFalse (by simp only [List.cons.injEq, h, false_and, not_false_eq_true])
  cases instDecidableEqListSrt tl1 tl2
  case isFalse h => exact isFalse (by simp only [List.cons.injEq, h, and_false, not_false_eq_true])
  exact isTrue (by simp [*])
| [], _::_ | _::_, [] => isFalse (by simp only [reduceCtorEq, not_false_eq_true])
| [], [] => isTrue rfl

instance instDecidableEqArraySrt : DecidableEq (Array Srt)
| ⟨l1⟩, ⟨l2⟩ => by
  cases instDecidableEqListSrt l1 l2
  · apply isFalse ; simp only [Array.mk.injEq, not_false_eq_true, *]
  · apply isTrue ; simp only [*]

instance instDecidableEq : DecidableEq Srt := fun s1 s2 => by
  cases s1
  <;> cases s2
  <;> (
    try (apply isFalse ; simp only [reduceCtorEq, not_false_eq_true] ; done)
    try (
      simp only [
        abstract.injEq, array.injEq, bag.injEq, bitVec.injEq,
        -- datatype.injEq,
        finiteField.injEq, float.injEq, function.injEq, seq.injEq, set.injEq,
        prod.injEq, uninterpreted.injEq,
      ]
      try exact inferInstance
      try exact instDecidableEq ..
      try exact instDecidableEqListSrt ..
      try exact Decidable.conj' (instDecidableEq ..) (instDecidableEq ..)
      try
        exact Decidable.conj'
          (instDecidableEq ..)
          (Decidable.conj' (instDecidableEqListSrt ..) (instDecidableEq ..))
    )
  )

end

/-- Boolean equality.

# TODO

- Probably should not use `instDecidableEq` for boolean equality; I'm not sure how efficient the
  code generated is.
-/
protected
def beq : Srt → Srt → Bool :=
  (instDecidableEq · · |>.decide)



namespace toString

/-- Specifies how to paren the string representation of a sort.

This only impacts the sort's top-level, paren for sub-sorts are decided by their super-sorts.
-/
inductive Paren
/-- Don't paren the sort at all. -/
| none
/-- Only paren if it's a function. -/
| ifFunction
/-- Only paren argument-having type constructors such as `(Array Bool)`. -/
| ifArgs
/-- Always paren *composite* sorts `(Array Bool)` but not leaf-sorts `Bool`. -/
| composite
deriving Inhabited, Hashable, DecidableEq, Ord

namespace Paren
/-- Maximum paren-ing.

**NB**: leaf-sorts such as `Srt.bool` are never paren-ed.
-/
def max : Paren := .composite

def fun? : Paren → Bool
| .none | .ifArgs => false
| .ifFunction | .composite => true

def args? : Paren → Bool
| .none | ifFunction => false
| .ifArgs | .composite => true

def apply? (self : Paren) : Paren → Bool
| .none => false
| .ifFunction => self.fun?
| .ifArgs => self.args?
| .composite => self = .composite

def apply (self : Paren) (that : Paren) (s : String) : String :=
  if self.apply? that then s!"({s})" else s
end Paren

end toString

open toString (Paren) in
/-- String representation. -/
protected partial
def toString (srt : Srt) (paren : Paren := .none) : String :=
  match srt with
  | .abstract kind => s!"abstract {kind}" |> paren.apply .ifArgs
  | .array idx elm => s!"Array {idx.toString .max} {elm.toString .max}" |> paren.apply .ifArgs
  | .bag elm => s!"Bag {elm.toString .max}" |> paren.apply .ifArgs
  | .bool => "Bool"
  | .bitVec n => s!"BitVec {n}" |> paren.apply .ifArgs
  -- | .datatype args =>
  --   "Datatype"
  --   |> args.foldl fun s arg => s!"{s} {arg.toString .max}"
  --   |> paren.apply .ifArgs
  | .finiteField n => s!"FiniteField {n}" |> paren.apply .ifArgs
  | .float exp sig => s!"Float {exp} {sig}" |> paren.apply .ifArgs
  | .function dom cod => s!"{dom.toString .ifFunction} → {cod.toString .none}"
  | .int => "Int"
  | .prod lft rgt => s!"{lft.toString .max} × {rgt.toString .ifFunction}"
  | .real => "Real"
  | .regex => "Regex"
  | .roundingMode => "RoundingMode"
  | .seq elm => s!"Seq {elm.toString .max}" |> paren.apply .ifArgs
  | .set elm => s!"Set {elm.toString .max}" |> paren.apply .ifArgs
  | .string => "String"
  | .unit => "Unit"
  | uninterpreted name => s!"Uninterpreted {name}" |> paren.apply .ifArgs

instance : ToString Srt := ⟨Srt.toString⟩



/-- Constructor from unsafe sorts.

This function recurses on sub-sorts retrieved by FFI: there is no chance to prove it terminates.
Hence the `maxDepth` optional parameter that sets an upper-bound on the recursion depth, causing
this function to crash if `maxDepth` is reached.
-/
def ofSort (sort : cvc5.Sort) (maxDepth : Nat := 100_000) : Res Srt :=
  aux sort maxDepth
  |>.context ls!"failed to convert cvc5 sort {sort} to `Cvc.Srt`"
where
  failKind {α} (k : cvc5.SortKind) : Res α := do
    let mut msg := s!"unexpected sort-kind `{k}`"
    Res.failInternal msg
  aux (sort : cvc5.Sort) : Nat → Res Srt
  | 0 => Res.failUser s!"maximum depth `{maxDepth}` reached"
  | maxDepth + 1 => do

    -- helpers
    let ofSort (s : cvc5.Sort) : Res Srt := aux s maxDepth
    let ofSorts (s : Array cvc5.Sort) : Res (List Srt) := Array.toList <$> s.mapM ofSort
    let ofSort? (s? : Except cvc5.Error cvc5.Sort) : Res Srt := s? >>= ofSort
    let ofSorts? (s? : Except cvc5.Error (Array cvc5.Sort)) : Res (List Srt) := s? >>= ofSorts

    -- let's do this
    match sort.getKind with

    -- leaves
    | .BOOLEAN_SORT => return .bool
    | .INTEGER_SORT => return .int
    | .REAL_SORT => return .real
    | .REGLAN_SORT => return .regex
    | .STRING_SORT => return .string
    | .ROUNDINGMODE_SORT => return .roundingMode
    | .FINITE_FIELD_SORT => .finiteField <$> sort.getFiniteFieldSize
    | .BITVECTOR_SORT => .bitVec <$> UInt32.toNat <$> sort.getBitVectorSize
    | .FLOATINGPOINT_SORT =>
      let exp ← sort.getFloatingPointExponentSize
      let sig ← sort.getFloatingPointSignificandSize
      return .float exp sig

    -- nodes
    | .UNINTERPRETED_SORT =>
      (.uninterpreted ∘ toString) <$> ofSort? sort.getUninterpretedSortConstructor
    | .BAG_SORT => .bag <$> ofSort? sort.getBagElementSort
    | .SEQUENCE_SORT => .seq <$> ofSort? sort.getSequenceElementSort
    | .SET_SORT => .set <$> ofSort? sort.getSetElementSort
    | .ARRAY_SORT =>
      return .array (← ofSort? sort.getArrayIndexSort) (← ofSort? sort.getArrayElementSort)
    | .TUPLE_SORT =>
      let rec doit (acc : Srt → Srt) : List Srt → Srt
        | [] => acc .unit
        | [srt] => srt
        | hd::tl@(_::_) => doit (acc <| Srt.prod hd ·) tl
      doit id <$> ofSorts? sort.getTupleSorts
    | .FUNCTION_SORT =>
      let cod ← ofSort? sort.getFunctionCodomainSort
      match ← ofSorts? sort.getFunctionDomainSorts with
      | doms@(_ :: _) =>
         -- careful that it must be a `foldr` here
        return doms.foldr .function cod
      | [] => Res.failInternal s!"illegal function sort, domain is empty"

    -- currently unsupported sorts
    | k@.ABSTRACT_SORT =>
      -- let kind ← sort.getAbstractedKind >>= Kind.ofSort
      -- return .abstract kind
      failKind k
    | k@.DATATYPE_SORT =>
      -- let args ← ofSorts sort.getInstantiatedParameters
      -- return .datatype args
      failKind k

    -- unexpected sorts
    | k@.NULLABLE_SORT => failKind k
    | k@.NULL_SORT => failKind k
    | k@.UNDEFINED_SORT_KIND => failKind k
    | k@.INTERNAL_SORT_KIND => failKind k
    | k@.LAST_SORT_KIND => failKind k


abbrev isFunction : Srt → Bool
| .function _ _ => true
| _ => false

abbrev is_function (srt : Srt) : Prop := srt.isFunction

example : DecidablePred is_function := inferInstance


abbrev isArith : Srt → Bool
| .int | .real => true
| _ => false

abbrev is_arith (srt : Srt) : Prop := srt.isArith

example : DecidablePred is_arith := inferInstance

theorem is_arith_def (srt : Srt) : srt.is_arith ↔ (srt = .int ∨ srt = .real) := by
  cases srt <;> simp

end Srt
