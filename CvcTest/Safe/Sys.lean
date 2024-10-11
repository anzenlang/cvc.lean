/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import CvcTest.Safe.Init



namespace Cvc.Safe.Test

open Smt


/-! ## Code for a simple induction-check library  -/
namespace Sys

structure SVar (F : Type → Type) (α : Type)
extends ValueOfSafeTerm α where
mkRaw ::
  val : F α

namespace SVar

def Untyped (F : Type → Type) : Type 1 :=
  (α : Type) × SVar F α

def untype (self : SVar F α) : Untyped F :=
  ⟨_, self⟩

protected abbrev Decl := SVar (fun _ => String)
protected abbrev Term := SVar Term
protected abbrev BVar := SVar BVar
protected abbrev Value := SVar id

instance : Coe (SVar F α) (F α) where
  coe svar := svar.val

def mk [I : ValueOfSafeTerm α] (val : F α) : SVar F α :=
  ⟨I, val⟩

def mk' (α : Type) [ValueOfSafeTerm α] (val : F α) : SVar F α :=
  mk val

def mk'' : ValueOfSafeTerm α → F α → SVar F α :=
  fun _ => mk

def mkDecl [ValueOfSafeTerm α] (name : String) : SVar.Decl α :=
  mk name

def mkDecl' (α : Type) [ValueOfSafeTerm α] (name : String) : SVar.Decl α :=
  mkDecl name

protected def I (self : SVar F α) : ValueOfSafeTerm α :=
  self.toValueOfSafeTerm

def mapM [Monad m] {F F' : Type → Type} (self : SVar F α) (f : F α → m (F' α)) : m (SVar F' α) := do
  let val ← f self
  return mk'' self.I val

def map : SVar F α → (F α → F' α) → SVar F' α :=
  mapM (m := Id)

def init [ToSafeSrt α] (self : SVar.Decl α) : SmtM (SVar.Term α) :=
  self.mapM (declareFun · α)

def bvar [ToSafeSrt α] (self : SVar.Decl α) : SmtM (SVar.BVar α) := do
  self.mapM (Term.mkBVar · α)

def getVal (self : SVar.Term α) : Smt.SatM (SVar.Value α) := do
  let _ := self.I
  self.mapM getValue

def getPre (self : SVar.Decl α) : SVar.Decl α :=
  self.map "reserved_pre_".append

def mapName (self : SVar.Decl α) (f : String → β) : SVar (fun _ => β) α :=
  self.map f

end SVar



class SVars (S : (Type → Type) → Type) where
  allDoM {m : Type → Type} [Monad m] :
    S F1 → (f : {α : Type} → [ValueOfSafeTerm α] → F1 α → m (F2 α)) → m (S F2)
  forIn {m : Type → Type} {β : Type} [Monad m] :
    S F → β → (SVar.Untyped F → β → m (ForInStep β)) → m β

namespace SVars

instance instForIn [SVars S] : ForIn m (S F) (SVar.Untyped F) :=
  ⟨SVars.forIn⟩

abbrev Untyped (F : Type → Type) : Type 1 :=
  Array (SVar.Untyped F)

abbrev Model S [SVars S] := S Id
abbrev Model' S [SVars S] := Model S
abbrev Model2 S [SVars S] := Model S × Model' S
abbrev BVars S [SVars S] := S BVar
abbrev BVars' S [SVars S] := S BVar
abbrev State S [SVars S] := S Term
abbrev State' S [SVars S] := S Term
abbrev PredT (m : Type → Type) S [SVars S] : Type := S Term → Term.ManagerT m (Term Bool)
abbrev PredT' := PredT
abbrev PredT2 m S [SVars S] := S Term → PredT m S
abbrev Pred S [SVars S] := PredT Id S
abbrev Pred' S [SVars S] := PredT' Id S
abbrev Pred2 := PredT2 Id
abbrev Decl S [SVars S] := S fun _ => String

variable [SVars S]

def mapM
  [Monad m]
  (self : S F)
  (f : {α : Type} → [ValueOfSafeTerm α] → F α → m (F' α))
: m (S F') :=
  SVars.allDoM self f

def map (self : S F) (f : {α : Type} → [ValueOfSafeTerm α] → F α → F' α) : S F' :=
  SVars.mapM (m := Id) self f

def init (self : Decl S) : SmtM (State S) :=
  allDoM self fun {α} _ name => declareFun name α

def bvars (self : Decl S) : SmtM (BVars S) :=
  allDoM self fun {α} _ name => Term.mkBVar name α

def bvarsList (self : BVars S) : SmtM Safe.BVars := do
  let mut bvars := Safe.BVars.empty
  for ⟨_, _, bvar⟩ in self do
    bvars := bvars.push bvar
  return bvars

def mapNames (self : S (fun _ => String)) (f : String → β) : S (fun _ => β) :=
  allDoM (m := Id) self fun {_} _ name => f name

def getVal (self : S Term) : Smt.SatM (S id) :=
  allDoM self fun {α} inst term =>
    let _ : ValueOfSafeTerm (id α) := by
      simp only [id]
      exact inferInstance
    Smt.getValue term
end SVars

export SVars (
  Model Model' Model2
  BVars BVars'
  State
  PredT PredT' PredT2
  Pred Pred' Pred2
  Decl
)

end Sys



structure SysT (m : Type → Type) (S : (Type → Type) → Type) [Sys.SVars S] where
  logic : Logic
  svars : Sys.Decl S
  prevSVars : Sys.Decl S :=
    Sys.SVars.map svars fun name => "reserved_pre_" ++ name
  init : Sys.PredT m S
  trans : Sys.PredT2 m S
  candidates : Array (String × Sys.Pred S)

abbrev Sys := SysT Id


namespace SysT
open Sys (SVars)

variable [Monad m] [SVars S] (self : SysT m S)

abbrev Model :=
  let _ := self
  Sys.SVars.Model S
abbrev Model? :=
  Option self.Model

abbrev Model' :=
  let _ := self
  Sys.SVars.Model' S
abbrev Model'? :=
  Option self.Model'

abbrev Model2 :=
  let _ := self
  Sys.SVars.Model2 S
abbrev Model2? :=
  Option self.Model2

abbrev BVar :=
  let _ := self
  Sys.SVars.BVars S
abbrev BVar' :=
  self.BVar

abbrev State :=
  let _ := self
  Sys.SVars.State S
abbrev State' :=
  let _ := self
  Sys.SVars.State' S
abbrev PredT :=
  let _ := self
  Sys.SVars.PredT m S
abbrev PredT' :=
  let _ := self
  Sys.SVars.PredT' m S
abbrev PredT2 :=
  let _ := self
  Sys.SVars.PredT2 m S
abbrev Pred :=
  let _ := self
  Sys.SVars.Pred S
abbrev Pred' :=
  let _ := self
  Sys.SVars.Pred' S
abbrev Pred2 :=
  let _ := self
  Sys.SVars.Pred2 S
abbrev Decl :=
  let _ := self
  Sys.SVars.Decl S

def checkInit : SmtT m self.Model? := do
  setLogic self.logic
  setOption .produceModels
  let terms ← SVars.init self.svars
  let init ← self.init terms
  assert init
  for (_, candidate) in self.candidates do
    let candidate ← candidate terms
    assert (← candidate.not)
  checkSat (m := m)
    (ifSat := some <$> SVars.getVal terms)
    (ifUnsat := return none)

def checkTrans : SmtT m self.Model2? := do
  setLogic self.logic
  setOption .produceModels

  let currSVars := self.svars
  let currTerms ← SVars.init currSVars
  let prevTerms ← SVars.init self.prevSVars

  let trans ← self.trans prevTerms currTerms
  assert trans

  for (_, candidate) in self.candidates do
    let prev ← candidate prevTerms
    assert prev
    let curr ← candidate currTerms
    assert (← curr.not)

  checkSat
    (ifSat := do
      let prev ← SVars.getVal prevTerms
      let curr ← SVars.getVal currTerms
      return some (prev, curr))
    (ifUnsat := return none)

/-- Computes the pre-image of `preds` assuming `assumptions` as a conjunction.

Using suffix `v@0` (`v@1`) for instantiation at the previous (current) state, this function
eliminates `v@1` in

- `φ = (∧ assumption@0) ∧ self.trans ∧ ¬ (∧ pred@1)`

where `assumption ∈ assumptions` and `pred ∈ preds`.

- `predsNegated`: if false `¬ (∧ pred@1)` becomes just `(∧ pred@1)` in `φ` above.
-/
def preimageOf
  (assumptions : Array (Sys.PredT Id S))
  (preds : Array (Sys.PredT' Id S))
  (predsNegated := true)
: SmtT m (Term Bool) := do
  setLogic self.logic
  setOption .produceInterpolants

  -- we're switching `prev ↔ curr` so that the resulting term mentions current variables
  let prevTerms ← SVars.init self.svars
  let currBVars ← SVars.bvars self.prevSVars

  -- assert all assumptions, these are in the previous state, *i.e.* the state we're **not**
  -- eliminating
  for assumption in assumptions do
    let a ← assumption prevTerms
    assert a

  -- prepare formula for QE

  -- current svars as terms, but they are actually bound variables to eliminate
  let currTerms := SVars.map currBVars BVar.toTerm
  -- `prevTerms` are actual terms, `currTerms` are bound variables
  let trans ← self.trans prevTerms currTerms
  -- accumulate current state predicates
  let mut predConj := #[]
  for pred in preds do
    let pred ← pred currTerms
    predConj := predConj.push pred
  let mut currPreds ← Term.mkAndN predConj
  if predsNegated then
    currPreds ← smt! ¬ currPreds
  let ψ ← smt! trans ∧ currPreds

  -- list of bound variables for QE (current svars)
  let currBVarsList ← SVars.bvarsList currBVars
  -- it's QE time
  let qConj ← ψ.mkExists currBVarsList

  getQuantifierElimination qConj

/-- Computes the preimage of the negated conjunction of the candidates.

- `forceCandidates`: if true then assert the conjunction of the candidates in the previous state,
  otherwise assert nothing on the previous state.

See also `SysT.preimageOf`.
-/
def preimageOfBad (forceCandidates := true) : SmtT m (Term Bool) :=
  let candidates := self.candidates.map Prod.snd
  self.preimageOf
    (assumptions := if forceCandidates then candidates else #[])
    (preds := candidates)
    (predsNegated := true)
end SysT
