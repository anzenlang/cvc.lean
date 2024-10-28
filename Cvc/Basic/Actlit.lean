/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Basic.Smt



/-! # Activation literals -/
namespace Cvc.Smt



structure Actlit where
private mkRaw ::
  term : Term

namespace Actlit

instance : Coe Actlit Term := ⟨term⟩

protected def reservedIdentPref :=
  "__cvc_reserved_actlit_"

def ident (n : Nat) :=
  s!"{Actlit.reservedIdentPref}_{n}__"

def isActlitIdent (s : String) :=
  s.startsWith Actlit.reservedIdentPref

def isActlitTerm (t : Term) : SmtM Bool := do
  t.toCvc5.getSymbol?
  |>.map isActlitIdent
  |>.getD false
  |> pure

private def mk : SmtM Actlit := do
  let idx ← SmtT.nextActlitIdx
  let symbol := ident idx
  Actlit.mkRaw <$> Smt.declareFun symbol (← Srt.bool)

/-- Asserts `a → t`.  -/
def assertActivation (a : Actlit) (t : Term) : SmtM Unit := do
  Smt.assert (← a.term.mkImplies t)

/-- Asserts `¬ a`. -/
def deactivate (a : Actlit) : SmtM Unit := do
  Smt.assert (← a.term.mkNot)

end Actlit

/-! ## `Smt` actlit helpers -/

/-- Creates an activation literal. -/
def mkActlit : SmtM Actlit := Actlit.mk

@[inherit_doc Actlit.assertActivation]
def assertActivation : Actlit → Term → SmtM Unit :=
  Actlit.assertActivation

@[inherit_doc Actlit.deactivate]
def deActlit : Actlit → SmtM Unit :=
  Actlit.deactivate

end Smt



/-! ## `Term` actlit helpers -/

namespace Term

/-- True if this term is an activation literal. -/
def isActlit : Term → SmtM Bool :=
  Smt.Actlit.isActlitTerm

@[inherit_doc Smt.Actlit.assertActivation]
def assertActivation : Smt.Actlit → Term → SmtM Unit :=
  Smt.Actlit.assertActivation

end Term
