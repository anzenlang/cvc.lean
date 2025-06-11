/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Term.Erased
import Cvc.Symbols.Defs



namespace Cvc



structure ESymbol (R : Symbol.Repr := (Symbol.Ident ·)) where
  srt : Srt
  getData : @R srt.toType Term.ToVal.Terms

namespace ESymbol

section variable (erased : ESymbol R)

abbrev type := erased.srt.toType

def mapM [Monad m] (f : R.srt erased.srt → m (R'.srt erased.srt)) : m (ESymbol R') :=
  return ⟨erased.srt, ← f erased.getData⟩

def map (f : R.srt erased.srt → R'.srt erased.srt) : ESymbol R' :=
  erased.mapM (m := Id) f

end

protected abbrev Ident := ESymbol (Symbol.Ident ·)
protected abbrev Term := ESymbol (Symbol.Term ·)
protected abbrev Value := ESymbol (Symbol.Value ·)

def mkIdent (name : String) (srt : Srt) : ESymbol.Ident :=
  ⟨srt, .mk name⟩


protected def toString (eSymbol : ESymbol.Ident) : String :=
  toString eSymbol.getData

instance : ToString ESymbol.Ident := ⟨ESymbol.toString⟩

def declare (ident : ESymbol.Ident) : Smt ESymbol.Term := do
  let ⟨srt, symbol⟩ := ident
  let term ← symbol.declare
  return ⟨srt, term⟩

def getSymbolETerm (term : ESymbol.Term) : ETerm :=
  ⟨term.srt, term.getData⟩

def getETerm (term : ESymbol.Term) : ETerm := term.getSymbolETerm

def getSymbolTerm (term : ESymbol.Term) : Term term.srt.toType :=
  term.getData

def getValue (term : ESymbol.Term) : Smt.Sat ESymbol.Value := do
  let ⟨srt, term⟩ := term
  let value ← term.getValUsing Term.ToVal.Terms
  return ⟨srt, value⟩

def getValueETerm (value : ESymbol.Value) : ETerm :=
  ⟨value.srt, value.getData⟩

def getValueTerm (value : ESymbol.Value) : Term value.srt.toType :=
  value.getData

def getValUsing (value : ESymbol.Value) (Val : Term.ToVal value.srt.toType) : Term.Build Val :=
  Val.ofTerm value.getValueTerm

def getVal (value : ESymbol.Value) [Val : Term.ToVal value.srt.toType] : Term.Build Val :=
  value.getValUsing Val

end ESymbol




namespace ESymbols

structure ByName (R : Symbol.Repr) : Type where
ofRBMap ::
  rbMap : RBMap String (ESymbol R)

namespace ByName

def mapM [Monad m] (symbols : ByName R)
  (f : (srt : Srt) → R.srt srt → m (R'.srt srt))
: m (ByName R') :=
  ofRBMap <$> symbols.rbMap.mapValM fun _name symbol => symbol.mapM (f symbol.srt)

def map (symbols : ByName R) (f : (srt : Srt) → R.srt srt → R'.srt srt) : ByName R' :=
  symbols.mapM (m := Id) f

protected def forIn [Monad m] (symbols : ByName R)
  (init : β) (f : (srt : Srt) → R.srt srt → β → m (ForInStep β))
: m β :=
  ForIn.forIn symbols.rbMap init fun (_name, symbol) => f symbol.srt symbol.getData

instance instSymbols : Symbols ByName where
  mapM symbols f := symbols.mapM fun srt => @f srt.toType Term.ToVal.Terms
  forIn symbols init f := symbols.forIn init fun srt => @f srt.toType Term.ToVal.Terms

protected abbrev Idents := instSymbols.Idents
protected abbrev Terms := instSymbols.Terms
protected abbrev Values := instSymbols.Values

Cvc.Symbols.aliasesFor! ByName ← ByName.Terms



def empty : ByName R := ⟨.empty⟩

def emptyIdents : ByName.Idents := empty

section variable (symbols : ByName R)

def insert! (name : String) (data : ESymbol R) : ByName R :=
  symbols.rbMap.insert name data |> ofRBMap

def insert? (name : String) (data : ESymbol R) : Option (ESymbol R) × ByName R :=
  let (prev?, map) := symbols.rbMap.insert' name data
  (prev?, ofRBMap map)

def insert (name : String) (data : ESymbol R) : Res (ByName R) :=
  let (prev?, symbols) := symbols.insert? name data
  if prev?.isSome then Error.throwUser
    s!"cannot insert symbol with name `{name}`: a symbol with this name already exists"
  else return symbols

def find? (name : String) : Option (ESymbol R) :=
  symbols.rbMap.find? name

def find (name : String) : Res (ESymbol R) :=
  if let some term := symbols.rbMap.find? name then return term
  else Error.throwUser s!"unknown symbol `{name}`"

def findSrt? (name : String) : Option Srt :=
  symbols.find? name |>.map ESymbol.srt

def findSrt (name : String) : Res Srt :=
  symbols.find name |>.map ESymbol.srt

def findAsSrt? (srt : Srt) (name : String) : Option (R.srt srt) := do
  let ⟨srt', repr⟩ ← symbols.find? name
  if h : srt' = srt then return h ▸ repr else none

def findAsSrt (srt : Srt) (name : String) : Res (R.srt srt) := do
  let ⟨srt', repr⟩ ← symbols.find name
  if h : srt' = srt then return h ▸ repr
  else Error.throwUser s!"symbol `{name} : {srt'}` cannot be typed as `{srt}`"

def findAs? (α : Type) [A : Srt.Bij α] (name : String) : Option (@R α Term.ToVal.Terms) := do
  let ⟨srt, h_bij⟩ := A
  let asSrt ← symbols.findAsSrt? srt name
  return by
    cases h_bij
    exact asSrt

def findAs (α : Type) [A : Srt.Bij α] (name : String) : Res (@R α Term.ToVal.Terms) := do
  let ⟨srt, h_bij⟩ := A
  let asSrt ← symbols.findAsSrt srt name
  return by
    cases h_bij
    exact asSrt

end



section variable (idents : ByName.Idents) (α : Type) [A : Srt.Bij α] (name : String)

def insertIdent! : ByName.Idents :=
  ESymbol.mkIdent name A.srt |> idents.insert! name

def insertIdent? : Option ESymbol.Ident × ByName.Idents :=
  ESymbol.mkIdent name A.srt |> idents.insert? name

def insertIdent : Res ByName.Idents :=
  ESymbol.mkIdent name A.srt |> idents.insert name

end



section variable (idents : ByName.Idents) (srt : Srt) (name : String)

def insertIdentSrt! : ByName.Idents :=
  ESymbol.mkIdent name srt |> idents.insert! name

def insertIdentSrt? : Option ESymbol.Ident × ByName.Idents :=
  ESymbol.mkIdent name srt |> idents.insert? name

def insertIdentSrt : Res ByName.Idents :=
  ESymbol.mkIdent name srt |> idents.insert name

end



section variable (terms : ByName.Terms)

/-- Retrieves the erased term of a name, fails if none. -/
def findETerm? (name : String) : Option ETerm := do
  let data ← terms.find? name
  return ETerm.mk data.srt data.getData

@[inherit_doc findETerm?]
def findETerm (name : String) : Res ETerm := do
  let data ← terms.find name
  return ETerm.mk data.srt data.getData

@[inherit_doc findETerm]
def get (name : String) : Res ETerm := terms.findETerm name

section variable (srt : Srt) (name : String)

/-- Retrieves the `Srt`-typed term of a name, fails if none or types do not match. -/
def findTermAsSrt? : Option (Term srt.toType) := do
  let eTerm ← terms.findETerm? name
  eTerm.asSrt? (srt := srt)

@[inherit_doc findTermAsSrt?]
def findTermAsSrt : Res (Term srt.toType) := do
  terms.findETerm name >>= ETerm.asSrt (srt := srt)

@[inherit_doc findTermAsSrt]
def getAsSrt : Res (Term srt.toType) := do
  terms.findTermAsSrt srt name

end

section variable (α : Type) [A : Srt.Bij α] (name : String)

/-- Retrieves the typed term of a name, fails if none or types do not match. -/
def findTermAs? : Option (Term α) := do
  terms.findETerm? name >>= ETerm.as? (α := α)

@[inherit_doc findTermAs?]
def findTermAs : Res (Term α) := do
  let eTerm ← terms.findETerm name
  eTerm.as α |>.context ls!"failed to type-check symbol `{name} : {eTerm.srt}` as `{A.srt}`"

@[inherit_doc findTermAs]
def getAs : Res (Term α) := do
  terms.findAs α name

end

end

end ByName
