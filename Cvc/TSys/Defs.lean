import Cvc.Safe

namespace Cvc.Safe.TSys

open Smt



structure SVar (F : Type → Type) (α : Type) extends ValueOfSafeTerm α where
protected mkRaw ::
  get : F α

namespace SVar

abbrev mk [ValueOfSafeTerm α] : F α → SVar F α := SVar.mkRaw inferInstance
abbrev mk' [ValueOfSafeTerm α] (F) : F α → SVar F α := mk (F := F)

def Untyped (F : Type → Type) : Type 1 :=
  (α : Type) × SVar F α

def untype (self : SVar F α) : Untyped F :=
  ⟨_, self⟩

abbrev Symbol := SVar (𝕂 String)
abbrev Term := SVar Safe.Term
abbrev BVar := SVar Safe.BVar
abbrev Value := SVar id

def mkSymbol [ValueOfSafeTerm α] (s : String) : Symbol α := mk s

instance [ValueOfSafeTerm α] : Coe String (Symbol α) := ⟨mkSymbol⟩

def mkSymbol' (α : Type) [ValueOfSafeTerm α] : String → Symbol α := mkSymbol

protected def unrollIdent (svar : Symbol α) (k : Nat) : String :=
  s!"__cvc_reserved_at_{k}_{svar.get}__"

abbrev inst (svar : SVar F α) := svar.toValueOfSafeTerm

instance (svar : SVar F α) : ValueOfSafeTerm α := svar.inst

def declare (s : Symbol α) (k : Nat) : SmtM (Term α) :=
  let _ := s.inst
  mk <$> declareFun (s.unrollIdent k) α

def bvar (s : Symbol α) (k : Nat) : SmtM (BVar α) :=
  let _ := s.inst
  mk <$> Safe.Term.mkBVar (s.unrollIdent k) α

def getVal (t : Term α) : Smt.SatM (Value α) :=
  let _ := t.inst
  mk <$> getValue (α := α) t.get

end SVar

class SVars (S : (Type → Type) → Type) where
  mapM {m : Type → Type} [Monad m] :
    S F1 → (f : {α : Type} → SVar F1 α → m (SVar F2 α)) → m (S F2)
  forIn {m : Type → Type} {β : Type} [Monad m] :
    S F → β → (SVar.Untyped F → β → m (ForInStep β)) → m β

namespace SVars

abbrev Untyped (F : Type → Type) : Type 1 :=
  Array (SVar.Untyped F)

abbrev Symbols [SVars S] := S (𝕂 String)

instance instForIn [SVars S] : ForIn m (S F) (SVar.Untyped F) :=
  ⟨SVars.forIn⟩

end SVars
