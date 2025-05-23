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



-- namespace Srt

-- /-- Maps cvc sorts to lean types. -/
-- abbrev toType : Srt → Type
-- | .bool => Bool
-- | .int => Int
-- | .array idx elm => Cvc.Array idx.toType elm.toType
-- | .function dom cod => dom.toType → cod.toType

-- instance : CoeSort Srt Type := ⟨Srt.toType⟩

-- /-- Lean-type-like string representation.

-- - `parenLevel`: specifies how to parenthesized the type string representation.

--   See `toString.noParenLevel`, `toString.funParenLevel`, `toString.arrayParenLevel`, *etc.*
-- -/
-- protected
-- def toString (srt : Srt) (parenLevel : Nat := 0) : String :=
--   match srt with
--   | .bool => "Bool" | .int => "Int"
--   | .array idx elm =>
--     arrayParen s!"Array {idx.toString arrayParenLevel} {elm.toString arrayParenLevel}"
--   | .function dom cod =>
--     funParen s!"{dom.toString funParenLevel} → {cod.toString noParenLevel}"
-- where
--   /-- Level at which nothing is parenthesized. -/
--   noParenLevel := 0
--   /-- Level above which function types are parenthesized. -/
--   funParenLevel := 1
--   /-- Level above which array types are parenthesized. -/
--   arrayParenLevel := 2

--   maxLevel := 1000
--   paren (lbound : Nat) : String → String :=
--     if lbound ≤ parenLevel then (s!"({·})") else id
--   funParen := paren funParenLevel
--   arrayParen := paren arrayParenLevel

-- /-- Paren-ed string representation. -/
-- def toParenString (srt : Srt) : String := srt.toString toString.maxLevel

-- instance : ToString Srt := ⟨Srt.toString⟩

-- end Srt

-- class AsSrt (α : Type) extends ToSrt α where
--   is_srt : α = toToSrt.srt := by simp <;> rfl

-- namespace AsSrt

-- @[simp]
-- theorem type_is_srt [A : AsSrt α] : α = A.srt :=
--   A.is_srt

-- instance : AsSrt Bool := {}
-- instance : AsSrt Int := {}
-- instance [I : AsSrt Idx] [E : AsSrt Elm] : AsSrt (Cvc.Array Idx Elm) := {}
-- instance [I : AsSrt Idx] [E : AsSrt Elm] : AsSrt (Idx → Elm) := {}

-- end AsSrt

-- namespace Array

-- /-- Constructor from a red-black map. -/
-- def ofRBMap [Ord Idx] [I : AsSrt Idx] [E : AsSrt Elm] (map : RBMap Idx Elm) : Cvc.Array Idx Elm :=
--   ⟨inferInstance, map, I.toToSrt, E.toToSrt⟩

-- /-- Constructor from a regular array. -/
-- def ofArray [AsSrt α] (array : Array α) : Cvc.Array Int α := Id.run do
--   let mut map := RBMap.empty
--   let mut cnt := 0
--   for val in array do
--     map := map.insert cnt val
--     cnt := cnt + 1
--   ofRBMap map

-- variable (a : Cvc.Array Idx Elm)

-- end Array



-- /-- A type-safe cvc term.

-- This is just a strongly-typed wrapper around `cvc5.Term`. Values of this type can only be created in
-- this module.
-- -/
-- structure Term (α : Type) extends AsSrt α where
-- /-- Private constructor.. -/
-- private ofUnsafe' ::
--   /-- Unsafe term accessor. -/
--   toUnsafe : cvc5.Term


-- namespace Term

-- /-- Cvc term management transformer monad. -/
-- abbrev T (m : Type → Type) :=
--   ExceptT Error (StateT Tm m)

-- /-- Cvc term management monad. -/
-- abbrev M := T Id



-- /-! ## Term-handling

-- Term-handling is mostly done in the `Env`/`EnvT` error-state monad which gives access to the term
-- manager.
-- -/



-- /-! ### Basic definitions -/

-- /-- Private constructor, same as `ofUnsafe'` with implicit `AsSrt α`. -/
-- private
-- def ofUnsafe [AsSrt α] (term : cvc5.Term) : Term α :=
--   Term.ofUnsafe' inferInstance term

-- /-- Private constructor, monadic version of `ofUnsafe`. -/
-- private
-- def ofUnsafeM [Monad m] [AsSrt α] (term : m cvc5.Term) : m (Term α) :=
--   Term.ofUnsafe <$> term

-- section variable (term : Term α)

-- instance instAsSrt : AsSrt α := term.toAsSrt

-- /-- Reframes the type parameter of a term as its `srt : Srt`. -/
-- abbrev asSrt : Term term.srt :=
--   term.is_srt ▸ term

-- /-- Facilitates pattern-matching on the sort (`Srt`) of a term. -/
-- def srtInspect (f : (srt : Srt) → Term srt → γ) : γ :=
--   f term.srt term.asSrt

-- /-- SMT-LIB string representation. -/
-- protected
-- def toString (t : Term α) : String :=
--   t.toUnsafe.toString

-- instance : ToString (Term α) := ⟨Term.toString⟩

-- end

-- export cvc5 (Kind)

-- /-- The kind of a term, see also `Variant`. -/
-- private
-- def kind (term : Term α) : Kind :=
--   term.toUnsafe.getKind

-- /-- The kids of a term. -/
-- private
-- def kids (term : Term α) : Array cvc5.Term :=
--   term.toUnsafe.getChildren



-- /-! ### Term manager and environment -/

-- namespace T variable [Monad m]

-- /-- Produces an error. -/
-- def fail (err : Error) : T m α :=
--   fun state => return (.error err, state)

-- instance : MonadLift M (T m) :=
--   ⟨fun code tm => return code tm⟩

-- instance : MonadLift (Except cvc5.Error) (T m) := ⟨
--   fun
--   | .ok res => return res
--   | .error err => fail (Error.ofCvc5 err)
-- ⟩

-- /-- Runs some term-handling code, yields the result and the term manager.

-- See also `run`.
-- -/
-- def run' (code : T m α) (tm : Tm) : m (Res α × Tm) := do
--   match ← code tm with
--   | (.ok val, tm) => return (.ok val, tm)
--   | (.error err, tm) => return (.error err, tm)

-- /-- Runs some `EnvT` code and yields the result. See also `run'`. -/
-- def run (code : T m α) (tm : Tm) : m (Res α) := do
--   Prod.fst <$> code.run' tm

-- end T

-- export T (fail)

-- /-- Lifts a monadic function over an unsafe term manager to `T`. -/
-- private
-- def liftFunM [Monad m] [Monad m'] [MonadLiftT m' (T m)]
--   (f : Tm → m' α)
-- : T m α := do
--   let manager ← get
--   f manager

-- /-- Lifts a function over an unsafe term manager to `T`. -/
-- private
-- def liftFun [Monad m] (f : Tm → α) : T m α :=
--   liftFunM (m' := Id) f



-- /-! ## Term construction -/

-- section
-- open Lean Elab Command

-- scoped syntax (name := termConstructors)
--   "Term.constructors!" (
--     withPosition(
--       docComment
--       "def " ident ", " ident
--         (ppSpace bracketedBinder)*
--         " : " term
--         -- declSig
--       " :="←
--       ppLine colGt term
--     )
--   )*
-- : command

-- @[command_elab termConstructors]
-- def termConstructorsElab : CommandElab
-- | `(
--   Term.constructors! $[
--     $doc:docComment
--     def $consId, $variantId
--       $[ $args:bracketedBinder ]* : Term $consType:term := $consDef:term
--   ]*
-- ) => do
--   let termName := ``Term
--   let variantTypeName := `Variant
--   let termId := Lean.mkIdent termName
--   let variantTypeId := Lean.mkIdent variantTypeName
--   let Mon := Lean.mkIdent ``M
--   let mut enumVariants := #[]
--   let mut toTermBranches : Array (TSyntax `Lean.Parser.Term.matchAlt) := #[]

--   let items := doc.zip <| consId.zip <| variantId.zip <| args.zip <| consType.zip consDef
--   for (doc, consId, variantId, args, consType, consDef) in items do
--     let (termType, variantType) ← do
--       let termType ← `(term| $termId $consType)
--       let variantType ← `(term| $variantTypeId $consType)
--       pure (termType, variantType)
--     -- elab the `Term` constructor's definition
--     let stx ← `(
--       $doc:docComment
--       def $consId:ident $[ $args ]* : $Mon ( $termType ) :=
--         $consDef:term
--     )
--     Command.elabCommand stx

--     -- build the `Variant` enum constructor/variant
--     let stx ← `(Lean.Parser.Command.ctor|
--       | $variantId:ident $[ $args ]* : $variantType
--     )
--     enumVariants := enumVariants.push stx

--     -- build the `toTerm` branch
--     let variantConsId := variantTypeName ++ variantId.getId |> Lean.mkIdent
--     let termId := ``Term ++ consId.getId |> Lean.mkIdent
--     let mut stxArgs : Array (TSyntax `term) := #[]
--     for arg in args do
--       match arg with
--       | `(bracketedBinder| ( $[$ids:ident]* : $_ty:term $[ := by $_:tacticSeq ]? ) )
--       | `(bracketedBinder| ( $[$ids:ident]* : $_ty:term ) ) =>
--         for id in ids do
--           stxArgs := stxArgs.push id
--       | _ => pure ()
--     let pat ← `(term| $variantConsId)
--     let expr ← `(term| $termId)
--     let stx ← `(Lean.Parser.Term.matchAltExpr|
--       | $pat $[ $stxArgs:term ]* => $expr $[ $stxArgs:term ]*
--     )
--     toTermBranches := toTermBranches.push stx

--   -- elab the `Variant` enum
--   let variantStx ← `(
--     /-- Enumerated version of `Term`, allows pattern-matching. -/
--     inductive $variantTypeId : Type → Type 1
--     $[ $enumVariants:ctor ]*
--   )
--   Command.elabCommand variantStx

--   -- elab `Variant` to `Term` conversion
--   let toTermId := Name.str variantTypeName "toTerm" |> Lean.mkIdent
--   let typeParamId := Lean.mkIdent `α
--   let toTermStx ← `(
--     /-- Converts itself to a `Term α`. -/
--     def $toTermId : $variantTypeId $typeParamId → $Mon ($termId $typeParamId)
--     $[ $toTermBranches:matchAlt ]*
--   )
--   Command.elabCommand toTermStx

-- | _ => throwUnsupportedSyntax

-- Term.constructors!
--   /-- Boolean constant. -/
--   def ofBool, bool (b : Bool) : Term Bool := do
--     liftFun (Tm.mkBoolean · b) |> ofUnsafeM

--   /-- Boolean negation. -/
--   def not, not (term : Term Bool) : Term Bool := do
--     let args := #[term.toUnsafe]
--     liftFunM (Tm.mkTerm · .NOT args) |> ofUnsafeM

--   /-- Integer constant. -/
--   def ofInt, int (i : Int) : Term Int := do
--     liftFunM (Tm.mkInteger · i) |> ofUnsafeM

--   /-- If-then-else. -/
--   def ite, ite (cnd : Term Bool) (thn els : Term α) : Term α :=
--     let _ := thn.instAsSrt
--     let args := #[cnd.toUnsafe, thn.toUnsafe, els.toUnsafe]
--     liftFunM (Tm.mkTerm · .ITE args) |> ofUnsafeM

--   /-- Store on arrays. -/
--   def store, store (array : Term (Cvc.Array Idx Val))
--     (idx : Term Idx) (val : Term Val)
--   : Term (Cvc.Array Idx Val) :=
--     let (_I, _E) := (idx.instAsSrt, val.instAsSrt)
--     let args := #[array.toUnsafe, idx.toUnsafe, val.toUnsafe]
--     liftFunM (Tm.mkTerm · cvc5.Kind.STORE args) |> ofUnsafeM

--   /-- Equality. -/
--   def eqN, eqN
--     (terms : Array (Term α))
--     (eq_srt : 2 ≤ terms.size := by (try simp) <;> omega)
--   : Term Bool :=
--     let args := terms.map Term.toUnsafe
--     liftFunM (Tm.mkTerm · cvc5.Kind.EQUAL args) |> ofUnsafeM


-- /-! ## Term manipulation -/

-- @[inherit_doc cvc5.Term.substitute]
-- def substitute
--   (term : Term α) (substs : Array ((β : Type) × Term β × Term β))
-- : M (Term α) := do
--   let _ := term.instAsSrt
--   let substs := substs.map fun ⟨_, t, r⟩ => (t.toUnsafe, r.toUnsafe)
--   term.toUnsafe.substitute substs |> Term.ofUnsafeM

-- #check Variant


-- namespace deconsAux

-- private
-- def failArity {α : Type} {β : Type u} : (expected : String) → (array : Array α) → Res β :=
--   (Res.failInternal s!"expected {·} child term(s), got {Array.size ·}")

-- private
-- def failKind {α : Type u} : (expected : String) → (kind : cvc5.Kind) → Res α :=
--   (Res.failInternal s!"expected {·} term-kind, got `{·}`")

-- private
-- def failSrt {α : Type u} : (expected : String) → (srt : Srt) → Res α :=
--   (Res.failInternal s!"expected {·} term-sort, got `{·}`")

-- variable (term : Term α)

-- private
-- def oneKid.{u} : Res.{u} (Up cvc5.Term) :=
--   match term.toUnsafe.getChildren with
--   | #[t1] => return Up.up t1
--   | array => failArity "exactly one" array

-- private
-- def twoKids.{u} : Res.{u} (Up (cvc5.Term × cvc5.Term)) :=
--   match term.toUnsafe.getChildren with
--   | #[t1, t2] => return Up.up (t1, t2)
--   | array => failArity "exactly two" array

-- private
-- def threeKids.{u} : Res.{u} (Up (cvc5.Term × cvc5.Term × cvc5.Term)) :=
--   match term.toUnsafe.getChildren with
--   | #[t1, t2, t3] => return Up.up (t1, t2, t3)
--   | array => failArity "exactly three" array

-- private
-- def many1Kids.{u} : Res.{u} (Up ((kids : Array cvc5.Term) ×' 1 < kids.size)) :=
--   let kids := term.toUnsafe.getChildren
--   if valid : 1 < kids.size
--   then return ⟨kids, valid⟩ else failArity "one or more" kids

-- private
-- def many2Kids.{u} : Res.{u} (Up ((kids : Array cvc5.Term) ×' 2 < kids.size)) :=
--   let kids := term.toUnsafe.getChildren
--   if valid : 2 < kids.size
--   then return ⟨kids, valid⟩ else failArity "two or more" kids

-- private
-- def adaptSrt [A : AsSrt α] {Tgt : Srt} (v : Variant α) : Res (Variant Tgt) :=
--   if h : Tgt = A.srt
--   then h ▸ Res.ok (A.type_is_srt ▸ v)
--   else failSrt Tgt.toString A.srt


-- private
-- def adaptBool : (α : Srt) → (v : Variant Bool) → Res (Variant α)
-- | .bool, v => by exact .ok v
-- | srt, _ => failSrt "Bool" srt
-- private
-- def adaptInt : (α : Srt) → (v : Variant Bool) → Res (Variant α)
-- | .bool, v => by exact .ok v
-- | srt, _ => failSrt "Bool" srt

-- end deconsAux

-- open deconsAux in
-- def deconsAux (α : Srt) (term : Term α) : Res.{1} (Variant α) :=
--   match h : (term.kind, α) with
--   | (.CONST_BOOLEAN, .bool) => do
--       let ⟨kid⟩ ← oneKid term
--       let ⟨b⟩ ← kid.getBooleanValue |> Res.lift1
--       by
--         cases Prod.ext_iff.mp h |>.right
--         exact .ok (Variant.bool b)
--   | (.EQUAL, .bool) => do
--     let ⟨⟨kids, valid⟩⟩ ← many2Kids term
--     let kids' := kids.map Term.ofUnsafe
--     sorry
--     -- | (.CONST_INTEGER, .int) =>
--     --   let ⟨kid⟩ ← oneKid term
--     --   let ⟨b⟩ ← kid.getBooleanValue |> Res.lift1
--     --   exact Variant.int b
--   | _ => Res.failInternal s!"\
--     unsupported/unexpected term-kind `{term.kind}` for `Term {term.srt.toParenString}`\
--   "

-- -- open toVariantAux in
-- -- def toVariant' [a : ToSrt α] : (t : Term α) → Res.{1} (Variant α) := by
-- --   let ⟨srt, valid⟩ := a
-- --   cases valid
-- --   exact aux srt
-- -- where
-- --   aux (α : Srt) (t : Term α) : Res (Variant α) :=
-- --     match t.kind with
-- --     | .CONST_BOOLEAN => do
-- --       let ULift.up kid ← (oneKid t).up1
-- --       let ⟨b⟩ ← kid.getBooleanValue |> Res.lift1
-- --       return .bool b
-- --     | _ => sorry
