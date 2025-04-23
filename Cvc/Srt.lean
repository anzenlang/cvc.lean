/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Init.Data.Nat.Power2

import cvc5

import Cvc.Init



namespace Cvc

open _root_ renaming ULift → Up

open cvc5 renaming TermManager → Tm



/-- A cvc sort, `Sort`-coercion realized by `Srt.toType`. -/
inductive Srt
| abstract (args : Array Srt)
| array (idx elm : Srt)
| bag (elm : Srt)
| bool
| bitVec (exp : Nat)
| datatype (args : Array Srt)
| finiteField (size : Nat)
| float (exp sig : UInt32)
| function (dom : Array Srt) (cod : Srt)
| int | real
| regex
| roundingMode
| seq (elm : Srt)
| set (elm : Srt)
| string
| tuple (elms : Array Srt)
| uninterpreted (constructor : Srt)

namespace Srt

protected
abbrev sigOfSortKind : cvc5.SortKind → Type
| .INTERNAL_SORT_KIND
| .UNDEFINED_SORT_KIND
| .NULL_SORT => Empty
| .ABSTRACT_SORT => Array cvc5.Sort
| .ARRAY_SORT => cvc5.Sort × cvc5.Sort
| .BAG_SORT => cvc5.Sort
| .BOOLEAN_SORT => Unit
| .BITVECTOR_SORT => Nat
| .DATATYPE_SORT => Array cvc5.Sort
| .FINITE_FIELD_SORT => Nat
| .FLOATINGPOINT_SORT => UInt32 × UInt32
| .FUNCTION_SORT => Array cvc5.Sort × cvc5.Sort
| .INTEGER_SORT
| .REAL_SORT
| .REGLAN_SORT
| .ROUNDINGMODE_SORT => Unit
| .SEQUENCE_SORT => cvc5.Sort
| .SET_SORT => cvc5.Sort
| .STRING_SORT => Unit
| .TUPLE_SORT => Array cvc5.Sort
| .NULLABLE_SORT => Empty
| .UNINTERPRETED_SORT => cvc5.Sort

def sigDataOfSort (s : cvc5.Sort) : Res (Srt.sigOfSortKind s.getKind) := by
  cases s.getKind <;> (simp only [Srt.sigOfSortKind] ; try exact .ok ())
  case INTERNAL_SORT_KIND => exact failKind s.getKind
  case UNDEFINED_SORT_KIND => exact failKind s.getKind
  case NULL_SORT => exact failKind s.getKind
  case ABSTRACT_SORT => exact .ok s.getInstantiatedParameters
  case ARRAY_SORT => exact do
    let idx ← s.getArrayIndexSort
    let elm ← s.getArrayElementSort
    return (idx, elm)
  case BAG_SORT => exact liftM s.getBagElementSort
  case BITVECTOR_SORT => exact do
    let size ← s.getBitVectorSize
    return size.toNat.nextPowerOfTwo
  case DATATYPE_SORT => exact .ok s.getInstantiatedParameters
  case FINITE_FIELD_SORT => exact liftM s.getFiniteFieldSize
  case FLOATINGPOINT_SORT => exact do
    let exp ← s.getFloatingPointExponentSize
    let sig ← s.getFloatingPointSignificandSize
    return (exp, sig)
  case FUNCTION_SORT => exact do
    let args ← s.getFunctionDomainSorts
    let cod ← s.getFunctionCodomainSort
    return (args, cod)
  case SEQUENCE_SORT => exact liftM s.getSequenceElementSort
  case SET_SORT => exact liftM s.getSetElementSort
  case TUPLE_SORT => exact liftM s.getTupleSorts
  case NULLABLE_SORT => exact failKind s.getKind
  case UNINTERPRETED_SORT => exact liftM s.getUninterpretedSortConstructor
where
  failKind {α} (k : cvc5.SortKind) (desc? : Option String := none) : Res α := do
    let mut msg := s!"unexpected sort-kind `{k}`"
    if let some desc := desc? then
      msg := s!"{desc}, {msg}"
    Res.failInternal msg

/-- Unsafe-to-safe sort conversion with a max depth to avoid `partial` annotation. -/
def ofSort.withMaxDepth : (maxDepth : Nat) → cvc5.Sort → Res Srt
| 0, s => Res.failInternal s!"\
  maximum depth reached during unsafe sort conversion, current sub-sort is `{s}`\
"
| maxDepth + 1, s => do
  let ofSort := withMaxDepth maxDepth
  let data ← sigDataOfSort s
  by
    revert data
    cases s.getKind <;> (simp only [Srt.sigOfSortKind] ; intro data ; try contradiction)
    case ABSTRACT_SORT => exact .abstract <$> data.mapM ofSort
    case ARRAY_SORT => exact return .array (← ofSort data.fst) (← ofSort data.snd)
    case BAG_SORT => exact .bag <$> ofSort data
    case BOOLEAN_SORT => exact return .bool
    case BITVECTOR_SORT => exact return .bitVec data
    case DATATYPE_SORT => exact .datatype <$> data.mapM ofSort
    case FINITE_FIELD_SORT => exact return .finiteField data
    case FLOATINGPOINT_SORT => exact return .float data.fst data.snd
    case FUNCTION_SORT => exact return .function (← data.fst.mapM ofSort) (← ofSort data.snd)
    case INTEGER_SORT => exact return .int
    case REAL_SORT => exact return .real
    case REGLAN_SORT => exact return .regex
    case ROUNDINGMODE_SORT => exact return .roundingMode
    case SEQUENCE_SORT => exact .seq <$> ofSort data
    case SET_SORT => exact .set <$> ofSort data
    case STRING_SORT => exact return .string
    case TUPLE_SORT => exact .tuple <$> data.mapM ofSort
    case UNINTERPRETED_SORT => exact .uninterpreted <$> ofSort data

def ofSort (s : cvc5.Sort) : Res Srt :=
  ofSort.withMaxDepth 100_000 s
  |>.lcontext fun () => s!"failed to convert unsafe sort `{s}`"

end Srt

class ToSrt (α : Type) where private mk ::
  srt : Srt

protected
structure Array (Idx Elm : Type) extends Ord Idx where
mk' ::
  toMap : RBMap Idx Elm
  IdxToSrt : ToSrt Idx
  ElmToSrt : ToSrt Elm

protected
structure Bag (Elm : Type) extends Ord Elm where
mk ::
  toMap : RBMap Elm Nat
  ElmToSrt : ToSrt Elm

namespace Bag variable [Ord Elm] [E : ToSrt Elm]

def empty : Cvc.Bag Elm :=
  ⟨inferInstance, RBMap.empty, inferInstance⟩

section variable (bag : Cvc.Bag Elm) (elm : Elm)

def contains : Bool :=
  match bag.toMap.find? elm with
  | none | some 0 => false
  | some (_ + 1) => true

def erase : Cvc.Bag Elm :=
  { bag with toMap := bag.toMap.erase elm }

def replace : (count : Nat) → Cvc.Bag Elm
| 0 => bag.erase elm
| count => { bag with toMap := bag.toMap.insert elm count}

def countDo (f : Nat → α) : α :=
  bag.toMap.findD elm 0 |> f

def countMap (f : Nat → Nat) : Cvc.Bag Elm :=
  bag.countDo elm f |> bag.replace elm

def insert (count : Nat := 1) : Cvc.Bag Elm :=
  bag.countMap elm (· + count)

def remove (count : Nat := 1) : Cvc.Bag Elm :=
  bag.countMap elm (· - count)

end

end Bag

protected
structure Set (Elm : Type) extends Ord Elm where
mk' ::
  toSet : RBSet Elm
  ElmToSrt : ToSrt Elm

protected
structure Regex where
  toString : String

namespace ToSrt

instance : ToSrt Bool := ⟨.bool⟩
instance : ToSrt Int := ⟨.int⟩
instance : ToSrt Rat := ⟨.real⟩

/-- Enforces the IEEE 754 standard.

Based on [wikipedia].

[wikipedia]: https://en.wikipedia.org/wiki/Double-precision_floating-point_format#IEEE_754_double-precision_binary_floating-point_format:_binary64
-/
instance : ToSrt Float :=
  ⟨.float 11 53⟩

variable [A : ToSrt α] [B : ToSrt β]

/-- Conversion from maps ("arrays" in SMT-LIB) to sort. -/
instance instToSrtCvcArray : ToSrt (Cvc.Array α β) := ⟨.array A.srt B.srt⟩
instance instToSrtBitVec : ToSrt (BitVec exp) := ⟨.bitVec exp⟩
instance instToSrtBag : ToSrt (Cvc.Bag α) := ⟨.bag A.srt⟩
instance instToSrtFunction : ToSrt (α → β) := ⟨.function #[A.srt] B.srt⟩
instance instToSrtRegex : ToSrt Regex := ⟨.regex⟩
/-- Conversion from arrays ("sequences" in SMT-LIB) to sort. -/
instance instToSrtArray : ToSrt (Array α) := ⟨.seq A.srt⟩
instance instToSrtSet : ToSrt (Cvc.Set α) := ⟨.set A.srt⟩
instance instToSrtString : ToSrt String := ⟨.string⟩
instance instToSrtProd : ToSrt (α × β) := ⟨.tuple #[A.srt, B.srt]⟩

end ToSrt



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
--       " :="
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
