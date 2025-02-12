import Cvc.Safe.Smt



namespace Cvc.Safe



/-! # Individual symbol representation -/



/-- An SMT (function) symbol: wraps an `F α`-value.

The `F` type constructor decides what this type actually means. For instance:

- `Symbol.Ident α := Symbol (fun _ => String) α` wraps a `String`, typically used to *declare*
  the function symbol;

- `Symbol.Term α := Symbol Term α` wraps a `Term α`, which is usually the result of a
  `Symbol.Ident` declaration.

- `Symbol.Value α := Symbol id α` wraps an `α`-value, useful to represent models produced by the
  solver for example when reporting a counterexample to something.
-/
structure Symbol (F : Type → Type) (α : Type)
extends ValueOfSafeTerm α where
protected mk'' ::
  get : F α

namespace Symbol

instance instCoeToInner : Coe (Symbol F α) (F α) :=
  ⟨get⟩

variable [ValueOfSafeTerm α]

abbrev mk {F} : F α → Symbol F α :=
  Symbol.mk'' inferInstance

abbrev mk' (F) : F α → Symbol F α :=
  mk (F := F)

def Untyped (F : Type → Type) : Type 1 :=
  (α : Type) × Symbol F α

def untype (self : Symbol F α) : Untyped F :=
  ⟨_, self⟩

protected abbrev Ident := Symbol fun _ => String
protected abbrev IdentAt : (k : Nat) → (α : Type) → Type :=
  fun _ => Symbol.Ident
protected abbrev Term := Symbol Safe.Term
protected abbrev TermAt : (k : Nat) → (α : Type) → Type :=
  fun _ => Symbol.Term
protected abbrev BVar := Symbol Safe.BVar
protected abbrev BVarAt : (k : Nat) → (α : Type) → Type :=
  fun _ => Symbol.BVar
protected abbrev Value := Symbol id
protected abbrev ValueAt : (k : Nat) → (α : Type) → Type :=
  fun _ => Symbol.Value

def mkIdent (ident : String) : Symbol.Ident α := mk ident
def mkTerm (term : Safe.Term α) : Symbol.Term α := mk term
def mkBVar (bVar : Safe.BVar α) : Symbol.BVar α := mk bVar
def mkValue (value : α) : Symbol.Value α := mk value

section

variable (symbol : Symbol F α)

instance instValueOfSafeTerm : ValueOfSafeTerm α :=
  symbol.toValueOfSafeTerm

abbrev inst := symbol.instValueOfSafeTerm

def mapM [Monad m]
  (f : [ValueOfSafeTerm α] → F α → m (G α))
: m (Symbol G α) :=
  Symbol.mk <$> f symbol

def map : ([ValueOfSafeTerm α] → F α → G α) → Symbol G α :=
  symbol.mapM (m := Id)

end



/-! ## `Ident`-specific helpers -/
namespace Ident

def mk := @Symbol.mkIdent

def mk' (α : Type) [ValueOfSafeTerm α] : String → Symbol.Ident α := mk

instance instCoeOfString : Coe String (Symbol.Ident α) := ⟨mk⟩

variable (ident : Symbol.Ident α)

protected
def toString : String := s!"|{ident.get}|"

instance instToString : ToString (Symbol.Ident α) := ⟨Ident.toString⟩

def declare : SmtM (Symbol.Term α) :=
  let _ := ident.inst
  ident.mapM (Smt.declareFun · α)

def bVar : Term.ManagerM (Symbol.BVar α) :=
  let _ := ident.inst
  ident.mapM (Term.mkBVar · α)

private def unrollIdent (ident : String) (k : Nat) : String :=
  s!"__reserved_cvc5_symbol_{ident}_unrolled_at_{k}"

def unrollAt (k : Nat) : Symbol.IdentAt k α :=
  let _ := ident.inst
  unrollIdent ident k |> Ident.mk

def declareAt (k : Nat) : SmtM (Symbol.TermAt k α) :=
  let _ := ident.inst
  ident.unrollAt k |>.declare

def bVarAt (k : Nat) : Term.ManagerM (Symbol.BVarAt k α) :=
  let _ := ident.inst
  ident.unrollAt k |>.bVar

end Ident

export Ident (declare bVar declareAt bVarAt)

namespace IdentAt

variable (ident : Symbol.IdentAt k α)

protected
def declare : SmtM (Symbol.TermAt k α ) := do
  let term : Symbol.TermAt k α ← by
    simp [Symbol.IdentAt] at ident
    exact ident.declare
  return term

end IdentAt



/-! ## `Term`-specific helpers -/
namespace Term

def mk := @Symbol.mkTerm

def mk' (α : Type) [ValueOfSafeTerm α] : Term α → Symbol.Term α :=
  mk

variable [ValueOfSafeTerm α] (term : Symbol.Term α)

protected
def toString : String := term.get.toString

instance instToString : ToString (Symbol.Term α) := ⟨Term.toString⟩

def getValue : Smt.SatM (Symbol.Value α) :=
  let _ := term.inst
  term.mapM (Smt.getValue (α := α) ·)

abbrev getVal := @getValue

end Term

export Term (getVal getValue)

namespace TermAt

variable (term : Symbol.TermAt k α)

protected
def toString : String := term.get.toString

instance instToString : ToString (Symbol.TermAt k α) := ⟨Term.toString⟩

def getValue : Smt.SatM (Symbol.ValueAt k α) :=
  let _ := term.inst
  term.mapM (Smt.getValue (α := α) ·)

abbrev getVal := @getValue

end TermAt

end Symbol



/-! # Many-symbol structure representation -/

class Symbols.{u, v} (Repr : (F : Type → Type) → Type) where
  /-- Monadic *map* over a `Repr _` -/
  mapM {m : Type → Type} [Monad m]
    (symbols : Repr F)
    (f : {α : Type} → Symbol F α → m (Symbol G α))
  : m (Repr G)

  /-- `ForIn`-like iteration function over `Symbol.Untyped _` elements. -/
  forIn {m : Type u → Type v} [Monad m]
    (symbols : Repr F)
    (acc : β)
    (code : Symbol.Untyped F → β → m (ForInStep β))
  : m β

  /-- Symbol identifier initialization. Don't use this directly, use `idents` instead. -/
  idents' : Repr (fun _ => String)

namespace Symbols

def map := @Symbols.mapM (m := id)

abbrev Untyped (F : Type → Type) : Type 1 :=
  Array (Symbol.Untyped F)

@[default_instance]
instance instForIn
  {Repr : (F : Type → Type) → Type}
  {F : Type → Type}
  [S : Symbols Repr]
: ForIn m (Repr F) (Symbol.Untyped F) where
  forIn repr acc f := S.forIn repr acc f

variable {Repr : (F : Type → Type) → Type}

def untype [Symbols Repr] (symbols : Repr F) : Untyped F := Id.run do
  let mut array := #[]
  for symbol in symbols do
    array := array.push symbol
  return array

abbrev Idents [Symbols Repr] := Repr fun _ => String
abbrev IdentsAt [Spec : Symbols Repr] : (k : Nat) → Type :=
  fun _ => Spec.Idents
abbrev Terms [Symbols Repr] := Repr Term
abbrev TermsAt [Spec : Symbols Repr] : (k : Nat) → Type :=
  fun _ => Spec.Terms
abbrev BVars [Symbols Repr] := Repr BVar
abbrev BVarsAt [Spec : Symbols Repr] : (k : Nat) → Type :=
  fun _ => Spec.BVars
abbrev Values [Symbols Repr] := Repr id
abbrev ValuesAt [Spec : Symbols Repr] : (k : Nat) → Type :=
  fun _ => Spec.Values
abbrev Concrete := @Values
abbrev ConcreteAt [Spec : Symbols Repr] : (k : Nat) → Type :=
  fun _ => Spec.Concrete

variable [Spec : Symbols Repr]

/-- Default identifiers for the symbols in a symbol structure. -/
def idents : Spec.Idents :=
  idents'

abbrev FunT m (α : Type) [ToSafeSrt α] := Spec.Terms → Term.ManagerT m (Term α)
abbrev Fun (α : Type) [ToSafeSrt α] := Spec.FunT (m := Id) α

protected abbrev FunctionT := @FunT
protected abbrev Function := @Fun

abbrev PredT m := Spec.FunT m Bool
abbrev Pred := Spec.Fun Bool
abbrev PredicateT := @PredT
abbrev Predicate := @Pred

abbrev RelT m := Spec.Terms → Spec.PredT m
abbrev Rel := Spec.RelT Id
abbrev RelationT := @RelT
abbrev Relation := @Rel



/-! ## `Ident`-specific helpers -/
namespace Idents

variable (idents : Spec.Idents)

def mapM [Monad m]
  (f : {α : Type} → Symbol.Ident α → m (Symbol G α))
: m (Repr G) :=
  Spec.mapM idents f

abbrev map := @mapM (m := Id)

def declare : SmtM Spec.Terms :=
  idents.mapM Symbol.declare

def bVars : Term.ManagerM Spec.BVars :=
  idents.mapM Symbol.bVar

def unrollAt (k : Nat) : SmtM (Spec.IdentsAt k) :=
  idents.map (Symbol.Ident.unrollAt · k)

def declareAt (k : Nat) : SmtM (Spec.TermsAt k) :=
  idents |>.mapM (Symbol.Ident.declareAt · k)

def bVarsAt (k : Nat) : Term.ManagerM (Spec.BVarsAt k) :=
  idents |>.mapM (Symbol.Ident.bVarAt · k)

end Idents

export Idents (declare bVars unrollAt declareAt bVarsAt)

namespace IdentsAt

variable (idents : Spec.IdentsAt k)

def declare : SmtM (Spec.TermsAt k) :=
  idents.mapM Symbol.declare

end IdentsAt



/-! ## `Term`-specific helpers -/
namespace Terms

variable (terms : Spec.Terms)

def mapM [Monad m]
  (f : {α : Type} → Symbol.Term α → m (Symbol G α))
: m (Repr G) :=
  Spec.mapM terms f

abbrev map := @mapM (m := Id)

def getVals : Smt.SatM Spec.Values :=
  terms.mapM Symbol.getVal
abbrev getValues := @getVals
abbrev getModel := @getVals

end Terms

export Terms (getVals getValues getModel)

namespace TermsAt

variable (terms : Spec.TermsAt k)

def getVals : Smt.SatM Spec.Values := by
  simp [Symbols.TermsAt] at terms
  exact (terms : Spec.Terms).getVals
abbrev getValues := @getVals
abbrev getModel := @getVals

end TermsAt

end Symbols
