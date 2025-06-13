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
  getData : R srt

namespace ESymbol

section variable (erased : ESymbol R)

abbrev type := erased.srt.toType

def mapM [Monad m] (f : R erased.srt → m (R' erased.srt)) : m (ESymbol R') :=
  return ⟨erased.srt, ← f erased.getData⟩

def map (f : R erased.srt → R' erased.srt) : ESymbol R' :=
  erased.mapM (m := Id) f

end

protected abbrev Ident := ESymbol (Symbol.Ident ·)
protected abbrev Term := ESymbol (Symbol.Term ·)
protected abbrev Value := ESymbol (Symbol.Value ·)

protected def toString (symbol : ESymbol R) [ToString (R symbol.srt)] : String :=
  toString symbol.getData

instance : ToString ESymbol.Ident := ⟨(ESymbol.toString ·)⟩
instance : ToString ESymbol.Term := ⟨(ESymbol.toString ·)⟩
instance : ToString ESymbol.Value := ⟨(ESymbol.toString ·)⟩

def mkIdent (name : String) (α : Type) [IsSrt α] : ESymbol.Ident :=
  ⟨getSrt α, .mk name⟩

namespace Ident variable (ident : ESymbol.Ident)

def mk := @ESymbol.mkIdent

def declare : Smt ESymbol.Term :=
  return ⟨ident.srt, ← ident.getData.declare⟩

end Ident

namespace Term variable (term : ESymbol.Term)

def toTerm : Term term.srt := term.getData

def toETerm : ETerm := ⟨term.srt, term.toTerm⟩

instance : Coe ESymbol.Term ETerm := ⟨toETerm⟩

def getValue : Smt.Sat ESymbol.Value :=
  return ⟨term.srt, ← term.getData.getValue⟩

end Term

namespace Value variable (value : ESymbol.Value)

def toValue : Value value.srt := value.getData

def toEValue : EValue := ⟨value.srt, value.toValue⟩

instance : Coe ESymbol.Value EValue := ⟨toEValue⟩

end Value

end ESymbol




namespace ESymbols

structure ByName (R : Symbol.Repr) : Type where
ofRBMap ::
  rbMap : RBMap String (ESymbol R)

namespace ByName

def mapM [Monad m] (symbols : ByName R)
  (f : (srt : Srt) → R srt → m (R' srt))
: m (ByName R') :=
  ofRBMap <$> symbols.rbMap.mapValM fun _name symbol => symbol.mapM (f symbol.srt)

def map (symbols : ByName R) (f : (srt : Srt) → R srt → R' srt) : ByName R' :=
  symbols.mapM (m := Id) f

protected def forIn [Monad m] (symbols : ByName R)
  (init : β) (f : (srt : Srt) → R srt → β → m (ForInStep β))
: m β :=
  ForIn.forIn symbols.rbMap init fun (_name, symbol) => f symbol.srt symbol.getData

instance instSymbols : Symbols ByName where
  mapM symbols f := symbols.mapM fun _srt => f
  forIn symbols init f := symbols.forIn init fun _srt => f

protected abbrev Idents := instSymbols.Idents
protected abbrev Terms := instSymbols.Terms
protected abbrev Values := instSymbols.Values

Cvc.Symbols.aliasesFor! ByName ← ByName.Terms



def empty : ByName R := ⟨.empty⟩

def emptyIdents : ByName.Idents := empty

section variable (symbols : ByName R)

private def genericInsert! (name : String) (data : ESymbol R) : ByName R :=
  symbols.rbMap.insert name data |> ofRBMap

private def genericInsert? (name : String) (data : ESymbol R) : Option (ESymbol R) × ByName R :=
  let (prev?, map) := symbols.rbMap.insert' name data
  (prev?, ofRBMap map)

private def genericInsert (name : String) (data : ESymbol R) : Res (ByName R) :=
  let (prev?, symbols) := symbols.genericInsert? name data
  if prev?.isSome then Error.throwUser
    s!"cannot insert symbol with name `{name}`: a symbol with this name already exists"
  else return symbols

def find? (name : String) : Option (ESymbol R) :=
  symbols.rbMap.find? name

def find (name : String) : Res (ESymbol R) :=
  if let some term := symbols.rbMap.find? name then return term
  else Error.throwUser s!"unknown symbol `{name}`"

def findMapOr (name : String) (f : ESymbol R → α) (getDefault : Unit → α) : α :=
  if let some s := symbols.find? name then f s else getDefault ()

def findSrt? (name : String) : Option Srt :=
  symbols.find? name |>.map ESymbol.srt

def findSrt (name : String) : Res Srt :=
  symbols.find name |>.map ESymbol.srt

def findAsSrt? (srt : Srt) (name : String) : Option (R srt) := do
  let ⟨srt', repr⟩ ← symbols.find? name
  if h : srt' = srt then return h ▸ repr else none

def findAsSrt (srt : Srt) (name : String) : Res (R srt) := do
  let ⟨srt', repr⟩ ← symbols.find name
  if h : srt' = srt then return h ▸ repr
  else Error.throwUser s!"symbol `{name} : {srt'}` cannot be typed as `{srt}`"

def findMapOrAsSrt (srt : Srt) (name : String) (f : R srt → α) (getDefault : Unit → α) : α :=
  if let some s := symbols.findAsSrt? srt name then f s else getDefault ()

def findAs? (α : Type) [A : IsSrt α] (name : String) : Option (R α) := do
  let ⟨srt, h_bij⟩ := A
  let asSrt ← symbols.findAsSrt? srt name
  return by
    cases h_bij
    exact asSrt

def findAs (α : Type) [A : IsSrt α] (name : String) : Res (R α) := do
  let ⟨srt, h_bij⟩ := A
  let asSrt ← symbols.findAsSrt srt name
  return by
    cases h_bij
    exact asSrt

def findMapOrAs (α : Type) [A : IsSrt α]
  (name : String) (f : R α → β) (getDefault : Unit → β)
: β := if let some s := symbols.findAs? α name then f s else getDefault ()

end



namespace Idents

def empty := emptyIdents

section variable (idents : ByName.Idents) (name : String) (α : Type) [A : IsSrt α]

def insert! : ByName.Idents :=
  ESymbol.mkIdent name A.srt |> idents.genericInsert! name

def insert? : Option ESymbol.Ident × ByName.Idents :=
  ESymbol.mkIdent name A.srt |> idents.genericInsert? name

def insert : Res ByName.Idents :=
  ESymbol.mkIdent name A.srt |> idents.genericInsert name

end

end Idents



namespace Terms variable (terms : ByName.Terms) (name : String)

def find? : Option ESymbol.Term := ByName.find? terms name

def find : Res ESymbol.Term := ByName.find terms name

def findETerm? : Option ETerm := ESymbol.Term.toETerm <$> terms.find? name

def findETerm : Res ETerm := ESymbol.Term.toETerm <$> terms.find name

end Terms

end ByName
