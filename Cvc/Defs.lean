/-
Copyright (c) 2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Lean.Parser

import Std.Data.HashMap.Basic

import Cvc.Basic.Batteries
import Cvc.Basic.Logic
import Cvc.Basic.Srt
import Cvc.Basic.Error



namespace Cvc open cvc5 renaming TermManager → Tm



/-! ## Environment: `EnvT`, `Env` -/



protected class Scope : Prop where
/-- Private constructor. -/
private ofUnit ::
  /-- Private projection to an irrelevant proof, never used. -/
  private toUnit : True

namespace Scope

def Stx.ident := ``Cvc.Scope |> Lean.mkIdent

end Scope



/-- State of the environment monad. -/
structure Env.State [Cvc.Scope] : Type where
/-- Constructor from a term manager. -/
private mk ::
  /-- `cvc5`'s term manager. -/
  private manager : Tm
  /-- Logic builder, used to track the logic necessary to express the terms actually built.

  Updated when building terms.
  -/
  private logic : Logic.Builder := Logic.Builder.mk

namespace Env.State

/-- Creates a new environment state. -/
private def new [Cvc.Scope] : cvc5.Env State := ({manager := ·}) <$> cvc5.TermManager.new

/-- Creates a new environment state for a specific scope. -/
private def newIn (S : Cvc.Scope) : cvc5.Env State := new

end Env.State



/-- Cvc environment monad transformer.

It should almost always be the case that `MonadLiftT BaseIO m`.
-/
def EnvT [Cvc.Scope] (m : Type → Type) (α : Type) : Type :=
  Env.State → m (Except Error α × Env.State)

/-- Cvc environment monad, in `BaseIO`.

This monad is compatible with `IO`.
-/
abbrev Env [Cvc.Scope] (α : Type) : Type :=
  EnvT BaseIO α

namespace EnvT

instance [Cvc.Scope] [Monad m] : Monad (EnvT m) where
  pure a state := return (.ok a, state)
  bind a f state := do
    match ← a state with
    | (.ok a, state) => f a state
    | (.error e, state) => return (.error e, state)

instance [Cvc.Scope] [Monad m] [MonadLiftT BaseIO m] : MonadLift Env (EnvT m) where
  monadLift code state := do
    let res ← code state
    return res

instance [Cvc.Scope] [Monad m] : MonadLift m (EnvT m) where
  monadLift mCode state := return (← .ok <$> mCode, state)

instance [Cvc.Scope] [Monad m] : MonadLift (Except Error) (EnvT m) where
  monadLift exc state := return (exc, state)

instance [Cvc.Scope] [Monad m] : MonadLift (ExceptT Error m) (EnvT m) where
  monadLift exc state := return (← exc, state)

instance [Cvc.Scope] [Monad m] : MonadState Env.State (EnvT m) where
  get state := return (.ok state, state)
  set state _state := return (.ok (), state)
  modifyGet f state :=
    let (res, state) := f state
    return (.ok res, state)

instance [Cvc.Scope] [Monad m] : MonadExcept Error (EnvT m) where
  throw e state := return (.error e, state)
  tryCatch code errorDo state := do
    match ← code state with
    | pair@(.ok _, _) => return pair
    | (.error e, state) => errorDo e state

instance [Cvc.Scope] [Monad m] [MonadLiftT BaseIO m] : MonadLift IO (EnvT m) where
  monadLift ioCode state := do
    match ← ioCode.toBaseIO with
    | .ok a => return (.ok a, state)
    | .error e => return (toString e |> .io |> .error, state)

private instance [Cvc.Scope] [Monad m] : MonadLift (cvc5.EnvT m) (EnvT m) where
  monadLift unsafeCode state :=
    return ((← unsafeCode).mapError Error.ofUnsafe, state)

/-- Runs `EnvT` code. -/
def run [Monad m] [MonadLiftT BaseIO m]
  (code : [Cvc.Scope] → EnvT m α)
: m (Except Error α) := do
  let S : Cvc.Scope := ⟨True.intro⟩
  match ← Env.State.newIn S |>.run with
  | .ok state => Prod.fst <$> code state
  | .error e => return .error e

end EnvT



namespace Env variable [Cvc.Scope]

def Stx.ident := ``Env |> Lean.mkIdent

-- sanity
example : Monad Env := inferInstance
example : MonadLift BaseIO Env := inferInstance
example : MonadLift (Except Error) Env := inferInstance
example : MonadLift (ExceptT Error BaseIO) Env := inferInstance
example : MonadState Env.State Env := inferInstance
example : MonadExcept Error Env := inferInstance
example : MonadLift IO Env := inferInstance
example : MonadLift cvc5.Env Env := inferInstance

/-- Runs `Env` code. -/
def run (code : [Cvc.Scope] → Env α) : BaseIO (Except Error α) :=
  EnvT.run code

/-- Runs `Env` code in `IO`. -/
def runIO (code : [Cvc.Scope] → Env α) : IO α := do
  match ←run code with
  | .ok a => return a
  | .error e => throw <| IO.userError <| toString e

end Env



/-- Unsafe term manager accessor. -/
private def getTm [Cvc.Scope] [Monad m] : EnvT m Tm :=
  fun state => return (.ok state.manager, state)

/-- Runs `cvc5.Env` code given the environment's underlying term manager. -/
private def tmDoM [Cvc.Scope] [Monad m] (f : Tm → cvc5.EnvT m α) : EnvT m α :=
  getTm >>= (liftM ∘ f)

@[inherit_doc tmDoM]
private def tmDo [Cvc.Scope] [Monad m] (f : Tm → α) : EnvT m α :=
  tmDoM (pure ∘ f)



/-! ## Sorts -/


/-- Safe cvc5 sorts. -/
def Srt [Cvc.Scope] := cvc5.Sort

namespace Srt variable [Cvc.Scope]

def Stx.ident := ``Srt |> Lean.mkIdent

@[inherit_doc Tm.getBooleanSort]
def bool : Env Srt := tmDoM Tm.getBooleanSort
@[inherit_doc Tm.getIntegerSort]
def int : Env Srt := tmDoM Tm.getIntegerSort
@[inherit_doc Tm.getRealSort]
def real : Env Srt := tmDoM Tm.getRealSort
@[inherit_doc Tm.getRegExpSort]
def regex : Env Srt := tmDoM Tm.getRegExpSort
@[inherit_doc Tm.getRoundingModeSort]
def roundingMode : Env Srt := tmDoM Tm.getRoundingModeSort
@[inherit_doc Tm.getStringSort]
def string : Env Srt := tmDoM Tm.getStringSort

@[inherit_doc Tm.mkArraySort]
def array (idx elm : Srt) : Env Srt :=
  tmDoM fun tm => tm.mkArraySort idx elm

@[inherit_doc Tm.mkBitVectorSort]
def bitVec (size : UInt32) : Env Srt :=
  tmDoM fun tm => tm.mkBitVectorSort size

@[inherit_doc Tm.mkFloatingPointSort]
def float (exp sig : UInt32) : Env Srt :=
  tmDoM fun tm => tm.mkFloatingPointSort exp sig

@[inherit_doc Tm.mkFiniteFieldSort]
def finiteField (size : Nat) (base : UInt32 := 10) : Env Srt :=
  tmDoM fun tm => tm.mkFiniteFieldSort size base

@[inherit_doc Tm.mkFunctionSort]
def function (dom : Array Srt) (cod : Srt) : Env Srt :=
  tmDoM fun tm => tm.mkFunctionSort dom cod

@[inherit_doc Tm.mkPredicateSort]
def predicate (dom : Array Srt) : Env Srt :=
  tmDoM fun tm => tm.mkPredicateSort dom

@[inherit_doc Tm.mkTupleSort]
def tuple (dom : Array Srt) : Env Srt :=
  tmDoM fun tm => tm.mkTupleSort dom

@[inherit_doc Tm.mkUninterpretedSortConstructorSort]
def uninterpretedSortConstructor (arity : Nat) (symbol : String) : Env Srt :=
  tmDoM fun tm => tm.mkUninterpretedSortConstructorSort arity symbol

@[inherit_doc Tm.mkSetSort]
def set (sort : Srt) : Env Srt :=
  tmDoM fun tm => tm.mkSetSort sort
@[inherit_doc Tm.mkBagSort]
def bag (sort : Srt) : Env Srt :=
  tmDoM fun tm => tm.mkBagSort sort
@[inherit_doc Tm.mkSequenceSort]
def seq (sort : Srt) : Env Srt :=
  tmDoM fun tm => tm.mkSequenceSort sort

@[inherit_doc Tm.mkAbstractSort]
def abstract (kind : Srt.Kind) : Env Srt :=
  tmDoM fun tm => tm.mkAbstractSort kind

@[inherit_doc Tm.mkUninterpretedSort]
def uninterpreted (symbol : String) : Env Srt :=
  tmDoM fun tm => tm.mkUninterpretedSort symbol

@[inherit_doc Tm.mkNullableSort]
def nullable (sort : Srt) : Env Srt :=
  tmDoM fun tm => tm.mkNullableSort sort

@[inherit_doc Tm.mkParamSort]
def param (symbol : String) : Env Srt :=
  tmDoM fun tm => tm.mkParamSort symbol



/-- Constructor from an unsafe `cvc5` sort. -/
private def ofUnsafe (sort : cvc5.Sort) : Srt := sort

section variable (sort : Srt)

/-- Unsafe `cvc5` version of an `Srt`. -/
private def toUnsafe : cvc5.Sort := sort

@[inherit_doc cvc5.Sort.getKind]
def getKind : Env Srt.Kind := sort.toUnsafe.getKind |> Kind.ofUnsafe |> pure

@[inherit_doc getKind]
def Kind.ofSrt := sort.getKind

@[inherit_doc cvc5.Sort.isBoolean]
def isBool : Env Bool := return sort.toUnsafe.isBoolean
@[inherit_doc cvc5.Sort.isInteger]
def isInt : Env Bool := return sort.toUnsafe.isInteger
@[inherit_doc cvc5.Sort.isReal]
def isReal : Env Bool := return sort.toUnsafe.isReal
@[inherit_doc cvc5.Sort.isString]
def isString : Env Bool := return sort.toUnsafe.isString
@[inherit_doc cvc5.Sort.isRegExp]
def isRegexp : Env Bool := return sort.toUnsafe.isRegExp
@[inherit_doc cvc5.Sort.isRoundingMode]
def isRoundingMode : Env Bool := return sort.toUnsafe.isRoundingMode
@[inherit_doc cvc5.Sort.isBitVector]
def isBitVec : Env Bool := return sort.toUnsafe.isBitVector
@[inherit_doc cvc5.Sort.isFloatingPoint]
def isFloat : Env Bool := return sort.toUnsafe.isFloatingPoint
@[inherit_doc cvc5.Sort.isDatatype]
def isDatatype : Env Bool := return sort.toUnsafe.isDatatype
@[inherit_doc cvc5.Sort.isDatatypeConstructor]
def isDatatypeConstructor : Env Bool := return sort.toUnsafe.isDatatypeConstructor
@[inherit_doc cvc5.Sort.isDatatypeSelector]
def isDatatypeSelector : Env Bool := return sort.toUnsafe.isDatatypeSelector
@[inherit_doc cvc5.Sort.isDatatypeTester]
def isDatatypeTester : Env Bool := return sort.toUnsafe.isDatatypeTester
@[inherit_doc cvc5.Sort.isDatatypeUpdater]
def isDatatypeUpdater : Env Bool := return sort.toUnsafe.isDatatypeUpdater
@[inherit_doc cvc5.Sort.isFunction]
def isFunction : Env Bool := return sort.toUnsafe.isFunction
@[inherit_doc cvc5.Sort.isPredicate]
def isPredicate : Env Bool := return sort.toUnsafe.isPredicate
@[inherit_doc cvc5.Sort.isTuple]
def isTuple : Env Bool := return sort.toUnsafe.isTuple
@[inherit_doc cvc5.Sort.isNullable]
def isNullable : Env Bool := return sort.toUnsafe.isNullable
@[inherit_doc cvc5.Sort.isRecord]
def isRecord : Env Bool := return sort.toUnsafe.isRecord
@[inherit_doc cvc5.Sort.isArray]
def isArray : Env Bool := return sort.toUnsafe.isArray
@[inherit_doc cvc5.Sort.isFiniteField]
def isFiniteField : Env Bool := return sort.toUnsafe.isFiniteField
@[inherit_doc cvc5.Sort.isSet]
def isSet : Env Bool := return sort.toUnsafe.isSet
@[inherit_doc cvc5.Sort.isBag]
def isBag : Env Bool := return sort.toUnsafe.isBag
@[inherit_doc cvc5.Sort.isSequence]
def isSequence : Env Bool := return sort.toUnsafe.isSequence
@[inherit_doc cvc5.Sort.isUninterpretedSort]
def isUninterpreted : Env Bool := return sort.toUnsafe.isUninterpretedSort
@[inherit_doc cvc5.Sort.isUninterpretedSortConstructor]
def isUninterpretedSortConstructor : Env Bool :=
  return sort.toUnsafe.isUninterpretedSortConstructor
@[inherit_doc cvc5.Sort.isInstantiated]
def isInstantiated : Env Bool := return sort.toUnsafe.isInstantiated

@[inherit_doc cvc5.Sort.hasSymbol]
def hasSymbol : Env Bool := sort.toUnsafe.hasSymbol

@[inherit_doc cvc5.Sort.getSymbol]
def getSymbol : Env String := sort.toUnsafe.getSymbol
@[inherit_doc cvc5.Sort.getSymbol?]
def getSymbol? : Env (Option String) := return sort.toUnsafe.getSymbol?

@[inherit_doc cvc5.Sort.getFunctionArity]
def getFunctionArity : Env Nat := sort.toUnsafe.getFunctionArity
@[inherit_doc cvc5.Sort.getFunctionArity?]
def getFunctionArity? : Env (Option Nat) := return sort.toUnsafe.getFunctionArity?

@[inherit_doc cvc5.Sort.getFunctionDomainSorts]
def getFunctionDomain : Env (Array Srt) :=
  sort.toUnsafe.getFunctionDomainSorts
@[inherit_doc cvc5.Sort.getFunctionDomainSorts?]
def getFunctionDomain? : Env (Option (Array Srt)) :=
  return sort.toUnsafe.getFunctionDomainSorts?

@[inherit_doc cvc5.Sort.getFunctionCodomainSort]
def getFunctionCodomain : Env Srt :=
  sort.toUnsafe.getFunctionCodomainSort
@[inherit_doc cvc5.Sort.getFunctionCodomainSort?]
def getFunctionCodomain? : Env (Option Srt) :=
  return sort.toUnsafe.getFunctionCodomainSort?

@[inherit_doc cvc5.Sort.getArrayIndexSort]
def getArrayIdx : Env Srt :=
  sort.toUnsafe.getArrayIndexSort
@[inherit_doc cvc5.Sort.getArrayIndexSort?]
def getArrayIdx? : Env (Option Srt) :=
  return sort.toUnsafe.getArrayIndexSort?

@[inherit_doc cvc5.Sort.getArrayElementSort]
def getArrayElm : Env Srt :=
  sort.toUnsafe.getArrayElementSort
@[inherit_doc cvc5.Sort.getArrayElementSort?]
def getArrayElm? : Env (Option Srt) :=
  return sort.toUnsafe.getArrayElementSort?

@[inherit_doc cvc5.Sort.getSetElementSort]
def getSetElm : Env Srt :=
  sort.toUnsafe.getSetElementSort
@[inherit_doc cvc5.Sort.getSetElementSort?]
def getSetElm? : Env (Option Srt) :=
  return sort.toUnsafe.getSetElementSort?

@[inherit_doc cvc5.Sort.getBagElementSort]
def getBagElm : Env Srt :=
  sort.toUnsafe.getBagElementSort
@[inherit_doc cvc5.Sort.getBagElementSort?]
def getBagElm? : Env (Option Srt) :=
  return sort.toUnsafe.getBagElementSort?

@[inherit_doc cvc5.Sort.getSequenceElementSort]
def getSeqElm : Env Srt :=
  sort.toUnsafe.getSequenceElementSort
@[inherit_doc cvc5.Sort.getSequenceElementSort?]
def getSeqElm? : Env (Option Srt) :=
  return sort.toUnsafe.getSequenceElementSort?

@[inherit_doc cvc5.Sort.getAbstractedKind]
def getAbstractedKind : Env Kind :=
  sort.toUnsafe.getAbstractedKind
@[inherit_doc cvc5.Sort.getAbstractedKind?]
def getAbstractedKind? : Env (Option Kind) :=
  return sort.toUnsafe.getAbstractedKind?.map .ofUnsafe

@[inherit_doc cvc5.Sort.getUninterpretedSortConstructorArity]
def getUninterpretedSortConstructorArity : Env UInt32 :=
  sort.toUnsafe.getUninterpretedSortConstructorArity
@[inherit_doc cvc5.Sort.getUninterpretedSortConstructorArity?]
def getUninterpretedSortConstructorArity? : Env (Option UInt32) :=
  return sort.toUnsafe.getUninterpretedSortConstructorArity?

@[inherit_doc cvc5.Sort.getBitVectorSize]
def getBitVecSize : Env UInt32 :=
  sort.toUnsafe.getBitVectorSize
@[inherit_doc cvc5.Sort.getBitVectorSize?]
def getBitVecSize? : Env (Option UInt32) :=
  return sort.toUnsafe.getBitVectorSize?

@[inherit_doc cvc5.Sort.getFiniteFieldSize]
def getFiniteFieldSizes : Env Nat :=
  sort.toUnsafe.getFiniteFieldSize
@[inherit_doc cvc5.Sort.getFiniteFieldSize?]
def getFiniteFieldSize? : Env (Option Nat) :=
  return sort.toUnsafe.getFiniteFieldSize?

@[inherit_doc cvc5.Sort.getFloatingPointExponentSize]
def getFloatingPointExponentSizes : Env UInt32 :=
  sort.toUnsafe.getFloatingPointExponentSize
@[inherit_doc cvc5.Sort.getFloatingPointExponentSize?]
def getFloatingPointExponentSize? : Env (Option UInt32) :=
  return sort.toUnsafe.getFloatingPointExponentSize?

@[inherit_doc cvc5.Sort.getFloatingPointSignificandSize]
def getFloatingPointSignificandSizes : Env UInt32 :=
  sort.toUnsafe.getFloatingPointSignificandSize
@[inherit_doc cvc5.Sort.getFloatingPointSignificandSize?]
def getFloatingPointSignificandSize? : Env (Option UInt32) :=
  return sort.toUnsafe.getFloatingPointSignificandSize?

@[inherit_doc cvc5.Sort.getTupleLength]
def getTupleLengths : Env UInt32 :=
  sort.toUnsafe.getTupleLength
@[inherit_doc cvc5.Sort.getTupleLength?]
def getTupleLength? : Env (Option UInt32) :=
  return sort.toUnsafe.getTupleLength?

@[inherit_doc cvc5.Sort.getTupleSorts]
def getTupleSorts : Env (Array Srt) :=
  sort.toUnsafe.getTupleSorts
@[inherit_doc cvc5.Sort.getTupleSorts?]
def getTupleSorts? : Env (Option (Array Srt)) :=
  return sort.toUnsafe.getTupleSorts?

@[inherit_doc cvc5.Sort.getNullableElementSort]
def getNullableElementSort : Env Srt :=
  sort.toUnsafe.getNullableElementSort
@[inherit_doc cvc5.Sort.getNullableElementSort?]
def getNullableElementSort? : Env (Option Srt) :=
  return sort.toUnsafe.getNullableElementSort?

@[inherit_doc cvc5.Sort.getUninterpretedSortConstructor]
def getUninterpretedSortConstructor : Env Srt :=
  sort.toUnsafe.getUninterpretedSortConstructor
@[inherit_doc cvc5.Sort.getUninterpretedSortConstructor?]
def getUninterpretedSortConstructor? : Env (Option Srt) :=
  return sort.toUnsafe.getUninterpretedSortConstructor?

@[inherit_doc cvc5.Sort.getInstantiatedParameters]
def getInstantiatedParameters : Env (Array Srt) :=
  sort.toUnsafe.getInstantiatedParameters
@[inherit_doc cvc5.Sort.getInstantiatedParameters?]
def getInstantiatedParameters? : Env (Option (Array Srt)) :=
  return sort.toUnsafe.getInstantiatedParameters?

@[inherit_doc cvc5.Sort.instantiate]
def instantiate (params : Array Srt) : Env Srt :=
  sort.toUnsafe.instantiate (params.map toUnsafe)
@[inherit_doc cvc5.Sort.instantiate?]
def instantiate? (params : Array Srt) : Env (Option Srt) :=
  return sort.toUnsafe.instantiate? params

@[inherit_doc cvc5.Sort.substitute]
def substituteMap (map : Array (Srt × Srt)) : Env Srt := do
  let mut sorts := Array.mkEmpty map.size
  let mut sorts' := Array.mkEmpty map.size
  for (sort, sort') in map do
    sorts := sorts.push sort
    sorts' := sorts'.push sort'
  sort.toUnsafe.substitute sorts sorts'
@[inherit_doc cvc5.Sort.substitute]
def substitute (src tgt : Array Srt) :
  (h : src.size ≤ tgt.size := by (try simp) <;> grind) → Env Srt
:= fun _ =>
  let sorts := src.map toUnsafe
  let sorts' := tgt.take sorts.size |>.map toUnsafe
  sort.toUnsafe.substitute sorts sorts'



@[inherit_doc cvc5.Sort.toString]
protected def toSmtString : Env String :=
  return sort.toUnsafe.toString

end

end Srt



/-! ## Untyped terms -/



/-- Type-unsafe cvc5 terms. -/
def Term [Cvc.Scope] : Type := cvc5.Term

/-- An array of terms. -/
abbrev Terms [Cvc.Scope] : Type := Array Term



namespace Term variable [Cvc.Scope]



def Stx.ident := ``Term |> Lean.mkIdent

/-- Constructor from an unsafe `cvc5` term. -/
private def ofUnsafe (term : cvc5.Term) : Term := term

section variable (term : Term)

/-- Unsafe `cvc5` version of a `Term`. -/
private def toUnsafe : cvc5.Term := term

/-- The `Srt` of a term. -/
abbrev srt : Env Srt := return term.toUnsafe.getSort |> Srt.ofUnsafe

/-- SMT-LIB string representation. -/
def toSmtString (term : Term) : Env String :=
  return term.toUnsafe.toString

end



/-! ### Thread-unsafe functions and instances -/
namespace ThreadUnsafe

@[inherit_doc cvc5.Term.beq]
def beq! (t t' : Term) : Bool := t.toUnsafe.beq t'

/-- Hash of a term. -/
-- @[inherit_doc cvc5.Term.hash]
def hash! (t : Term) : UInt64 := t.toUnsafe.hash

scoped instance : Hashable Term := inferInstanceAs <| Hashable cvc5.Term
scoped instance : BEq Term := inferInstanceAs <| BEq cvc5.Term

end ThreadUnsafe



/-! ### Safe versions of thread-unsafe functions -/

@[inherit_doc cvc5.Term.beq]
def beq (t t' : Term) : Env Bool := return Term.ThreadUnsafe.beq! t t'

/-- The hash of a term. -/
-- @[inherit_doc cvc5.Term.hash]
def hash (t : Term) : Env UInt64 := return Term.ThreadUnsafe.hash! t



/-! ### Hash maps and sets -/

open scoped ThreadUnsafe in
/-- Hashmap for `Term`s. -/
def HMap (α : Type) : Type := Std.HashMap Term α

namespace HMap open scoped ThreadUnsafe variable (map : HMap α) open Std (HashMap)

/-- Explicitly accesses the underlying hashmap. -/
private def get : HMap α → HashMap Term α := id
@[inherit_doc HashMap.emptyWithCapacity]
def empty (capacity : Nat := 8) : HMap α := HashMap.emptyWithCapacity capacity
@[inherit_doc HashMap.insert]
def insert (key : Term) (val : α) : Env (HMap α) := return map.get.insert key val
@[inherit_doc HashMap.erase]
def erase (key : Term) : Env (HMap α) := return map.get.erase key
@[inherit_doc HashMap.get?]
def get? (key : Term) : Env (Option α) := return map.get.get? key
@[inherit_doc HashMap.contains]
def contains (key : Term) : Env Bool := return map.get.contains key
@[inherit_doc HashMap.size]
def size : Nat := map.get.size
@[inherit_doc HashMap.isEmpty]
def isEmpty : Bool := map.get.isEmpty
@[inherit_doc HashMap.keys]
def keys : List Term := map.get.keys
@[inherit_doc HashMap.toList]
def toList : List (Term × α) := map.get.toList

@[inherit_doc HashMap.foldM]
def foldM := @map.get.foldM
@[inherit_doc HashMap.fold]
def fold := @map.get.fold
@[inherit_doc HashMap.forM]
def forM := @map.get.forM
@[inherit_doc HashMap.forIn]
def forIn := @map.get.forIn

instance : ForM m (HMap α) (Term × α) := HashMap.instForMProd
instance : ForIn m (HMap α) (Term × α) := HashMap.instForInProd

end HMap

attribute [irreducible] HMap


/-! ### Term constructors. -/



/-! #### Lean-value injection -/

@[inherit_doc Tm.mkBoolean]
def bool (b : Bool) : Env Term :=
  tmDoM fun tm => Term.ofUnsafe <$> tm.mkBoolean b

@[inherit_doc Tm.mkInteger]
def int (i : Int) : Env Term :=
  tmDoM fun tm => Term.ofUnsafe <$> tm.mkInteger i

@[inherit_doc Tm.mkReal]
def rat (r : Rat) : Env Term :=
  tmDoM fun tm => Term.ofUnsafe <$> tm.mkRealOfRat r

@[inherit_doc Tm.mkReal]
def real (num : Int) (den : Nat) (h : den ≠ 0 := by (try simp) <;> grind) : Env Term :=
  tmDoM fun tm => Term.ofUnsafe <$> tm.mkReal num den



/-! #### Constant symbol creation -/

/-- Creates a constant symbol of some sort. -/
def symbol (name : String) (sort : Srt) : Env Term :=
  tmDoM fun tm => tm.mkConst sort name

/-- Creates a constant Boolean symbol. -/
def boolSymbol (name : String) : Env Term :=
  Srt.bool >>= symbol name

/-- Creates a constant integer symbol. -/
def intSymbol (name : String) : Env Term :=
  Srt.int >>= symbol name

/-- Creates a constant real symbol. -/
def realSymbol (name : String) : Env Term :=
  Srt.real >>= symbol name

/-- Creates a constant regular expression symbol. -/
def regexSymbol (name : String) : Env Term :=
  Srt.regex >>= symbol name

/-- Creates a constant regular expression symbol. -/
def roundingModeSymbol (name : String) : Env Term :=
  Srt.roundingMode >>= symbol name

/-- Creates a constant string symbol. -/
def stringSymbol (name : String) : Env Term :=
  Srt.string >>= symbol name



/-! #### Composite term creation -/



section variable (t t' : Term) (terms : Terms) (valid : 2 ≤ terms.size := by (try simp) <;> omega)

@[inherit_doc Tm.mkTerm, specialize opIndices]
def mk (op : Kind) (terms : Terms) (opIndices : Array Nat := #[]) : Env Term :=
  if opIndices.isEmpty
  then tmDoM fun tm => Term.ofUnsafe <$> tm.mkTerm op terms
  else tmDoM fun tm => do
    let op ← tm.mkOpOfIndices op opIndices
    Term.ofUnsafe <$> tm.mkTermOfOp op terms

def Stx.ident_mk := ``mk |> Lean.mkIdent

section open Lean.Parser

declare_syntax_cat op2Defs1

scoped syntax (name := op2Defs1Stx)
  term
  ppLine ppIndent(docComment ppLine ident)
  ppLine ppIndent(docComment ppLine ident)
: op2Defs1

scoped syntax (name := op2DefsStx)
  "op2Defs" (ppLine ppIndent(op2Defs1))+
: command

@[command_elab op2DefsStx]
def op2DefsElab : Lean.Elab.Command.CommandElab
| `(op2Defs $[ $inners:op2Defs1 ]*
) => do
  let arrayId := ``Array |> Lean.mkIdent
  let mut stxArray := Array.mkEmpty inners.size
  for inner in inners do
    let `(op2Defs1|
      $op:term $nAryDoc:docComment $nAryId:ident $binaryDoc:docComment $binaryId:ident
    ) := inner
      | Lean.Elab.throwUnsupportedSyntax
    let stx ← `(
      $nAryDoc:docComment
      def $nAryId [$(Scope.Stx.ident)] (terms : $arrayId $(Term.Stx.ident)) :
        (valid : 2 ≤ terms.size := by (try simp) <;> omega) → $(Env.Stx.ident) $(Term.Stx.ident)
      := fun _ => $(Term.Stx.ident_mk) $op terms

      $binaryDoc:docComment
      def $binaryId [$(Scope.Stx.ident)] (lft rgt : $(Term.Stx.ident)) :
        $(Env.Stx.ident) $(Term.Stx.ident)
      := $nAryId:ident #[lft, rgt]
    )
    stxArray := stxArray.push stx
  for stx in stxArray do
    Lean.Elab.Command.elabCommand stx
| _ => Lean.Elab.throwUnsupportedSyntax

end

op2Defs
  .EQUAL /-- N-ary equality. -/ mkEq /-- Binary equality. -/ eq
  .DISTINCT /-- N-ary pairwise non-equality. -/ mkDistinct /-- Binary non-equality. -/ distinct
  .IMPLIES /-- N-ary implication. -/ mkImplies /-- Binary implication. -/ implies
  .AND /-- N-ary conjunction. -/ mkAnd /-- Binary conjunction. -/ and
  .OR /-- N-ary disjunction. -/ mkOr /-- Binary disjunction. -/ or
  .XOR /-- N-ary exclusive-or. -/ mkXor /-- Binary exclusive-or. -/ xor
  .LT /-- N-ary less-than. -/ mkLt /-- Binary less-than. -/ lt
  .LEQ /-- N-ary less-than-or-equal-to. -/ mkLe /-- Binary less-than-or-equal-to. -/ le
  .GEQ /-- N-ary greater-than-or-equal-to. -/ mkGe /-- Binary greater-than-or-equal-to. -/ ge
  .GT /-- N-ary greater-than. -/ mkGt /-- Binary greater-than. -/ gt
  .ADD /-- N-ary addition. -/ mkAdd /-- Binary addition. -/ add
  .MULT /-- N-ary multiplication. -/ mkMul /-- Binary multiplication. -/ mul
  .DIVISION_TOTAL
    /-- N-ary total **real** division, division by `0` is `0`, left-associative. -/
    mkRealDivTotal
    /-- Binary total **real** division, division by `0` is `0`. -/
    realDivTotal
  .DIVISION
    /-- N-ary **real** division, division by `0` undefined, left-associative. -/
    mkRealDiv
    /-- Binary **real** division, division by `0` undefined. -/
    realDiv
  .INTS_DIVISION_TOTAL
    /-- N-ary total **integer** division, division by `0` is `0`, left-associative. -/
    mkIntDivTotal
    /-- Binary total **integer** division, division by `0` is `0`. -/
    intDivTotal
  .INTS_DIVISION
    /-- N-ary **integer** division, division by `0` undefined, left-associative. -/
    mkIntDiv
    /-- Binary **integer** division, division by `0` undefined. -/
    intDiv
  .SUB /-- N-ary division. -/ mkSub /-- Binary division. -/ sub

/-- Boolean negation of a term. -/
def not := mk .NOT #[t]

/-- If-then-else. -/
def ite (c t e : Term) := mk .ITE #[c, t, e]

/-- Function application. -/
def apply (f arg : Term) := mk .APPLY_UF #[f, arg]

/-- Total division. -/
def divTotal := mk .DIVISION_TOTAL #[t, t']

/-- Unary minus. -/
def neg := mk .NEG #[t]

/-- Power of two of an integer term. -/
def pow2 := mk .POW2 #[t]

/-- Integer modulus, modulus by `0` undefined. -/
def mod := mk .INTS_MODULUS #[t, t']

/-- Integer modulus, modulus by `0` is zero. -/
def modTotal := mk .INTS_MODULUS_TOTAL #[t, t']

/-- Absolute value over integers/reals. -/
def abs := mk .ABS #[t]

/-- Arithmetic power over integers/reals, both terms must have the same sort. -/
def pow := mk .POW #[t, t']

/-- Exponential of a real term. -/
def exp := mk .EXPONENTIAL #[t]

/-- Sine of a real term. -/
def sine := mk .SINE #[t]

/-- Cosine of a real term. -/
def cosine := mk .COSINE #[t]

/-- Tangent of a real term. -/
def tangent := mk .TANGENT #[t]

/-- Secant of a real term. -/
def secant := mk .SECANT #[t]

/-- Cosecant of a real term. -/
def cosecant := mk .COSECANT #[t]

/-- Cotangent of a real term. -/
def cotangent := mk .COTANGENT #[t]

/-- Arc-sine of a real term. -/
def arcSine := mk .ARCSINE #[t]

/-- Arc-cosine of a real term. -/
def arcCosine := mk .ARCCOSINE #[t]

/-- Arc-tangent of a real term. -/
def arcTangent := mk .ARCTANGENT #[t]

/-- Arc-secant of a real term. -/
def arcSecant := mk .ARCSECANT #[t]

/-- Arc-cosecant of a real term. -/
def arcCosecant := mk .ARCCOSECANT #[t]

/-- Arc-cotangent of a real term. -/
def arcCotangent := mk .ARCCOTANGENT #[t]

/-- Square root of a real term. -/
def sqrt := mk .SQRT #[t]

/-- Divisibility-by-`k` predicate over integer terms. -/
def divisible (k : Nat) := mk .DIVISIBLE #[t] (opIndices := #[k])



/-! #### Lean-value extraction -/



@[inherit_doc cvc5.Term.getBooleanValue?]
def boolVal? (t : Term) : Env (Option Bool) :=
  return t.toUnsafe.getBooleanValue?
@[inherit_doc cvc5.Term.getBooleanValue?]
def boolVal (t : Term) : Env Bool := do
  if let some b ← t.boolVal? then return b
  else throwUser "cannot retrieve `Bool` value of a non-constant term"

@[inherit_doc cvc5.Term.getIntegerValue?]
def intVal? (t : Term) : Env (Option Int) :=
  return t.toUnsafe.getIntegerValue?
@[inherit_doc cvc5.Term.getIntegerValue?]
def intVal (t : Term) : Env Int := do
  if let some b ← t.intVal? then return b
  else throwUser "cannot retrieve `Int` value of a non-constant term"

@[inherit_doc cvc5.Term.getRationalValue?]
def ratVal? (t : Term) : Env (Option Rat) :=
  return t.toUnsafe.getRationalValue?
@[inherit_doc cvc5.Term.getRationalValue?]
def ratVal (t : Term) : Env Rat := do
  if let some b ← t.intVal? then return b
  else throwUser "cannot retrieve `Rat` value of a non-constant term"

end

end Term



/-! ## Conversion to terms -/



/-- Conversion class from `α` to `Term`, with a `σ`-context. -/
class ToTermIn (σ α : Type) : Type where
  /-- Conversion to a `Term` in a `Cvc.Scope`, with a `σ`-context. -/
  toTermIn : [Cvc.Scope] → α → StateT σ Env Term

@[inherit_doc ToTermIn.toTermIn]
def toTermIn := @ToTermIn.toTermIn

/-- Context-free conversion class from `α` to `Term`.

See also `ToTermMin`.
-/
class ToTerm (α : Type) : Type where
  /-- Context-free conversion to a `Term` in a `Cvc.Scope`. -/
  toTerm : [Cvc.Scope] → α → Env Term

@[inherit_doc ToTerm.toTerm]
def toTerm := @ToTerm.toTerm

namespace ToTerm

instance toToTermIn [ToTerm α] : ToTermIn Unit α where
  toTermIn | a, state => return (← toTerm a, state)

end ToTerm



/-! ## Proof and proof rules -/

@[inherit_doc cvc5.Proof]
def Proof [Cvc.Scope] : Type := cvc5.Proof

namespace Proof variable [Cvc.Scope] (proof : Proof)

@[inherit_doc cvc5.ProofRule]
abbrev Rule := cvc5.ProofRule

@[inherit_doc cvc5.ProofRewriteRule]
abbrev RwRule := cvc5.ProofRewriteRule

/-- Constructor from an unsafe `cvc5` proof. -/
private def ofUnsafe (proof : cvc5.Proof) : Proof := proof

/-- Unsafe `cvc5` version of a `Proof`. -/
def toUnsafe : cvc5.Proof := proof

@[inherit_doc cvc5.Proof.getRule]
def getRule : Env Rule := return proof.toUnsafe.getRule

@[inherit_doc cvc5.Proof.getRewriteRule]
def getRewriteRule : Env RwRule := proof.toUnsafe.getRewriteRule

@[inherit_doc cvc5.Proof.getResult]
def getResult : Env Term := return proof.toUnsafe.getResult

@[inherit_doc cvc5.Proof.getChildren]
def getChildren : Env (Array Proof) := return proof.toUnsafe.getChildren

@[inherit_doc cvc5.Proof.getArguments]
def getArguments : Env Terms := return proof.toUnsafe.getArguments

end Proof



/-- A cvc5 solver instance. -/
structure Solver [Cvc.Scope] : Type where
private mk' ::
  get : cvc5.Solver
  log? : IO.Ref Bool
  logRef : IO.Ref String



namespace Env variable [Cvc.Scope]

def SatT (m : Type → Type) (α : Type) := EnvT m α
abbrev Sat (α : Type) := SatT BaseIO α

def UnsatT (m : Type → Type) (α : Type) := EnvT m α
abbrev Unsat (α : Type) := UnsatT BaseIO α

def UnknownT (m : Type → Type) (α : Type) := EnvT m α
abbrev Unknown (α : Type) := UnknownT BaseIO α

section variable [Monad m]

namespace Sat
instance : Monad (SatT m) := inferInstanceAs <| Monad <| EnvT m
instance : MonadExcept Error (SatT m) := inferInstanceAs <| MonadExcept Error <| EnvT m
instance : MonadLift (EnvT m) (SatT m) := ⟨id⟩
example [MonadLiftT BaseIO m] : MonadLiftT Sat (SatT m) := ⟨fun code state => code state⟩
--sanity
example : MonadLiftT m (SatT m) := inferInstance
example : MonadLiftT Env Sat := inferInstance

/-- Reports an unexpected result. -/
def unexpected : SatT m α := throwUser "unexpected *sat* result"
end Sat

namespace Unsat
instance : Monad (UnsatT m) := inferInstanceAs <| Monad <| EnvT m
instance : MonadExcept Error (UnsatT m) := inferInstanceAs <| MonadExcept Error <| EnvT m
instance : MonadLift (EnvT m) (UnsatT m) := ⟨id⟩
example [MonadLiftT BaseIO m] : MonadLiftT Unsat (UnsatT m) := ⟨fun code state => code state⟩
--sanity
example : MonadLiftT m (UnsatT m) := inferInstance
example : MonadLiftT Env Unsat := inferInstance

/-- Reports an unexpected result. -/
def unexpected : UnsatT m α := throwUser "unexpected *unsat* result"
end Unsat

namespace Unknown
instance : Monad (UnknownT m) := inferInstanceAs <| Monad <| EnvT m
instance : MonadExcept Error (UnknownT m) := inferInstanceAs <| MonadExcept Error <| EnvT m
instance : MonadLift (EnvT m) (UnknownT m) := ⟨id⟩
example [MonadLiftT BaseIO m] : MonadLiftT Unknown (UnknownT m) := ⟨fun code state => code state⟩
--sanity
example : MonadLiftT m (UnknownT m) := inferInstance
example : MonadLiftT Env Unknown := inferInstance

/-- Reports an unexpected result. -/
def unexpected : UnknownT m α := throwUser "unexpected *unknown* result"
end Unknown

end

end Env



namespace Solver variable [Cvc.Scope]

/-- Constructor from a unsafe `cvc5` solver. -/
private def ofUnsafe (name : String) (solver : cvc5.Solver) : Env Solver :=
  return ⟨solver, ← IO.mkRef false, ← IO.mkRef s!"; log for `{name}`"⟩


section variable (solver : Solver)

def getLog : Env String := solver.logRef.get

def log (lazy : Unit → Env String) : Env Unit := do
  if ← solver.log?.get then
    solver.logRef.modifyGet ((), s!"{·}\n\n{← lazy ()}")

def logComment (lazy : Unit → String) : Env Unit := do
  if ← solver.log?.get then
    let lines := lazy () |>.splitOn "\n"
    solver.logRef.modifyGet fun s => ((), lines.foldl (init := s ++ "\n") (s!"{·}\n; {·}"))

/-- Unsafe `cvc5` version of a `Solver`. -/
private def toUnsafe : cvc5.Solver := solver.get

def logCommands (on : Bool := true) : Env Unit :=
  solver.log?.set on



/-- Constructor. -/
def mk (name : String := "cvc5") (log? : Bool := false) : Env Solver := do
  let solver ← (tmDoM fun tm => cvc5.Solver.new tm) >>= ofUnsafe name
  solver.logCommands log?
  return solver

@[inherit_doc cvc5.Solver.parseCommands]
def parseSmtLib (smtLib : String) : Env Unit :=
  (fun _ => ()) <$> solver.toUnsafe.parseCommands smtLib

@[inherit_doc cvc5.Solver.setOption]
def setOption (opt val : String) : Env Unit := do
  let mut passAlong := true
  if opt = "log" then
    passAlong := false
    match val with
    | "true" => solver.logCommands true
    | "false" => solver.logCommands false
    | s => throwUser s!"expected `true` or `false` as value for option `log`, got `{s}`"
  solver.log fun () => return s!"(set-option :{opt} {val})"
  if passAlong then solver.toUnsafe.setOption opt val

@[inherit_doc cvc5.Solver.setLogic]
def setLogic (logic : Logic) : Env Unit := do
  solver.log fun () => return s!"(set-logic {logic.toSmtLib})"
  solver.toUnsafe.setLogic logic.toSmtLib

section variable (symbol : String)

@[inherit_doc cvc5.Solver.declareFun]
def declareFun (sorts : Array Srt) (sort : Srt) : Env Term :=
  Term.ofUnsafe <$> solver.toUnsafe.declareFun symbol sorts sort

/-- Declares a constant symbol. -/
def declareConst (sort : Srt) : Env Term :=
  solver.declareFun symbol #[] sort

/-- Declares a Boolean symbol. -/
def declareBool : Env Term := Srt.bool >>= solver.declareConst symbol
/-- Declares an integer symbol. -/
def declareInt : Env Term := Srt.int >>= solver.declareConst symbol
/-- Declares a real symbol. -/
def declareReal : Env Term := Srt.real >>= solver.declareConst symbol
/-- Declares a string symbol. -/
def declareString : Env Term := Srt.string >>= solver.declareConst symbol

end

@[inherit_doc cvc5.Solver.resetAssertions]
def resetAssertions : Env Unit := do
  solver.log fun () => return s!"(reset)"
  solver.toUnsafe.resetAssertions

@[inherit_doc cvc5.Solver.assertFormula]
def assert (term : Term) : Env Unit := do
  solver.log fun () => return s!"(assert {← term.toSmtString})"
  solver.toUnsafe.assertFormula term

/-- Asserts a term `t` under an activation term `act`: same as `assert`-ing `act → t`. -/
def activeAssert (act : Term) (t : Term) : Env Unit :=
  act.implies t >>= solver.assert

@[inherit_doc cvc5.Solver.checkSatAssuming]
def checkSat? (assuming : Terms := #[]) : Env CheckSat := do
  let res ← .ofUnsafe <$> solver.toUnsafe.checkSatAssuming assuming
  solver.log fun () => do
    if assuming.isEmpty then return s!"(check-sat)\n; {res}"
    else
      let mut s := "(check-sat-assuming ("
      for t in assuming do
        s := s!"{s}\n  {← t.toSmtString}"
      return s!"{s}\n))\n; {res}"
  return res

/-- Check-sat with optional assumptions and runs sat/unsat/unknown-mode-specific code. -/
def checkSatM [Monad m] [MonadLiftT BaseIO m]
  (assuming : Terms := #[])
  (ifSat : Env.SatT m α := Env.Sat.unexpected)
  (ifUnsat : Env.UnsatT m α := Env.Unsat.unexpected)
  (ifUnknown : Env.UnknownT m α := Env.Unknown.unexpected)
: EnvT m α := do
  match ← solver.checkSat? assuming with
  | .sat => ifSat
  | .unsat => ifUnsat
  | .unknown _ | .other _ => ifUnknown

@[inherit_doc checkSatM]
def checkSat
  (assuming : Terms := #[])
  (ifSat : Env.Sat α := Env.Sat.unexpected)
  (ifUnsat : Env.Unsat α := Env.Unsat.unexpected)
  (ifUnknown : Env.Unknown α := Env.Unknown.unexpected)
: Env α :=
  checkSatM (m := BaseIO) solver assuming ifSat ifUnsat ifUnknown

/-! ### Sat-mode-specific commands -/
section satMode

@[inherit_doc cvc5.Solver.getValue]
def getValue (term : Term) : Env.Sat Term := do
  solver.log fun () => return s!"(get-value\n  {← term.toSmtString}\n)"
  solver.toUnsafe.getValue term

@[inherit_doc cvc5.Solver.getValues]
def getValues (terms : Terms) : Env.Sat Terms := do
  solver.log fun () => do
    let mut s := "(get-values"
    for t in terms do
      s := s!"{s}\n  {← t.toSmtString}"
    return s ++ "\n)"
  solver.toUnsafe.getValues terms

/-- Same as `getValues` but produces a map from terms to their value. -/
def getValueMap (terms : Terms) : Env.Sat (Term.HMap Term) := do
  Term.HMap.empty terms.size
  |> terms.foldlM fun map term => solver.getValue term >>= map.insert term

@[inherit_doc cvc5.Solver.getModelDomainElements]
def getDomainElements (sort : Srt) : Env.Sat Terms := solver.toUnsafe.getModelDomainElements sort

end satMode



/-! ### Unsat-mode-specific commands -/
section unsatMode

@[inherit_doc cvc5.Solver.getUnsatCore]
def getUnsatCore : Env.Unsat Terms := do
  solver.log fun () => return s!"(get-unsat-core)"
  solver.toUnsafe.getUnsatCore

@[inherit_doc cvc5.Solver.getProof]
def getProof : Env.Unsat (Array Proof) := do
  solver.log fun () => return s!"(get-proof)"
  solver.toUnsafe.getProof

@[inherit_doc cvc5.Solver.proofToString]
def proofToString (proof : Proof) : Env.Unsat String := solver.toUnsafe.proofToString proof

end unsatMode

/-- Performs a check-sat, if *unsat* runs get-unsat-core. -/
def checkUnsatCore? (assuming : Terms := #[]) : Env (Option Terms) :=
  solver.checkSat assuming (ifSat := return none) (ifUnsat := some <$> solver.getUnsatCore)

end

end Solver



attribute [irreducible] Srt
attribute [irreducible] Term
attribute [irreducible] Proof

-- attribute [irreducible] EnvT
-- attribute [irreducible] Env.SatT
-- attribute [irreducible] Env.UnsatT
-- attribute [irreducible] Env.UnknownT
