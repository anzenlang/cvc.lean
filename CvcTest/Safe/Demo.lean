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

structure SVar (F : Type → Type) (α : Type) where
mkRaw ::
  val : F α
  instValueOfSafeTerm : ValueOfSafeTerm α

protected abbrev SVar.Decl := SVar (fun _ => String)
protected abbrev SVar.Term := SVar Term
protected abbrev SVar.Value := SVar id

namespace SVar

def mk' (α : Type) [I : ValueOfSafeTerm α] (name : String) : SVar.Decl α where
  val := name
  instValueOfSafeTerm := I

def mk [ValueOfSafeTerm α] (name : String) : SVar.Decl α := mk' α name

def init [ToSafeSrt α] (self : SVar.Decl α) : SmtM (SVar.Term α) := do
  let val ← declareFun self.val α
  return { val, instValueOfSafeTerm := self.instValueOfSafeTerm }

def doM [Monad m] (self : SVar F1 α) (f : F1 α → m (F2 α)) : m (SVar F2 α) := do
  let val ← f self.val
  return ⟨val, self.instValueOfSafeTerm⟩

def getVal (self : SVar.Term α) : Smt.SatM (SVar.Value α) := do
  let _ := self.instValueOfSafeTerm
  let inst := self.instValueOfSafeTerm
  let value ← getValue self.val
  return ⟨value, inst⟩

def getPre (self : SVar.Decl α) : SVar.Decl α where
  val := "reserved_pre_" ++ self.val
  instValueOfSafeTerm := self.instValueOfSafeTerm

def mapName (self : SVar.Decl α) (f : String → β) : SVar (fun _ => β) α where
  val := f self.val
  instValueOfSafeTerm := self.instValueOfSafeTerm

end SVar



class SVars (S : (Type → Type) → Type) where
  allDoM [Monad m] : S F1 → (f : {α : Type} → [ValueOfSafeTerm α] → F1 α → m (F2 α)) → m (S F2)

namespace SVars
variable [SVars S]

def init (self : S (fun _ => String)) : SmtM (S Term) := do
  allDoM self fun {α} _ name => declareFun name α

def mapNames (self : S (fun _ => String)) (f : String → β) : S (fun _ => β) :=
  allDoM (m := Id) self fun {_} _ name => f name

def getVal (self : S Term) : Smt.SatM (S id) :=
  allDoM self fun {α} inst term =>
    let _ : ValueOfSafeTerm (id α) := by
      simp only [id]
      exact inferInstance
    Smt.getValue term

abbrev Model S [SVars.{0} S] := S Id.{0}
abbrev Model' S [SVars.{0} S] := Model S × Model S
abbrev State S [SVars.{0} S] := S Term
abbrev PredT (m : Type → Type) S [SVars.{0} S] : Type := S Term → Term.ManagerT m (Term Bool)
abbrev PredT' m S [SVars.{0} S] := S Term → PredT m S
abbrev Pred S [SVars.{0} S] := PredT Id S
abbrev Pred' S [SVars.{0} S] := PredT' Id S
abbrev Decl S [SVars.{0} S] := S fun _ => String
end SVars

export SVars (Model Model' State PredT PredT' Pred Pred' Decl)

end Sys



structure SysT (m : Type → Type) (S : (Type → Type) → Type) [Sys.SVars S] where
  logic : Logic
  svars : Sys.Decl S
  init : Sys.PredT m S
  trans : Sys.PredT' m S
  candidates : Array (String × Sys.Pred S)

abbrev Sys := SysT Id


namespace SysT
open Sys (SVars)

variable [Monad m] [SVars S] (self : SysT m S)

abbrev State :=
  let _ := self
  S Term

def checkInit : SmtT m (Option (Sys.Model S)) := do
  setLogic self.logic
  setOption "produce-models" "true"
  let terms ← SVars.init self.svars
  let init ← self.init terms
  assert init
  for (_, candidate) in self.candidates do
    let candidate ← candidate terms
    assert (← candidate.not)
  checkSat (m := m)
    (ifSat := some <$> SVars.getVal terms)
    (ifUnsat := return none)

def checkTrans : SmtT m (Option (Sys.Model S × Sys.Model S)) := do
  setLogic self.logic
  setOption "produce-models" "true"

  let currSVars := self.svars
  let prevSVars := SVars.mapNames self.svars (fun name => "reserved_pre_" ++ name)
  let currTerms ← SVars.init currSVars
  let prevTerms ← SVars.init prevSVars

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
end SysT



/-! ## Demo -/
namespace sw

structure Vars (F : Type → Type) where
  reset : Sys.SVar F Bool
  startStop : Sys.SVar F Bool
  counting : Sys.SVar F Bool
  count : Sys.SVar F Int

namespace Vars
variable (self : Vars F)

def reset! := self.reset.val
def startStop! := self.startStop.val
def counting! := self.counting.val
def count! := self.count.val
end Vars

instance mySVars.instSVars : Sys.SVars Vars where
  allDoM self f := do
    let reset ← self.reset.doM f
    let startStop ← self.startStop.doM f
    let counting ← self.counting.doM f
    let count ← self.count.doM f
    return ⟨reset, startStop, counting, count⟩

def vars : Vars (fun _ => String) where
  reset := Sys.SVar.mk "reset"
  startStop := Sys.SVar.mk "startStop"
  counting := Sys.SVar.mk "counting"
  count := Sys.SVar.mk "count"

def init : Sys.Pred Vars := smt! state =>
  (state.count! = 0) ∧ (state.counting! = state.startStop!)

def trans : Sys.Pred' Vars := smt! prev curr =>
  let counting ←
    curr.counting! = if curr.startStop! then ¬ prev.counting! else prev.counting!
  let countDef ←
    if curr.reset! then 0
    else prev.count! + (if prev.counting! then 1 else 0)
  let count ←
    curr.count! = countDef
  counting ∧ count

def count_pos : String × Sys.Pred Vars :=
  ("0 ≤ count", smt! state => state.count! ≥ 0)

def count_ne_minus_seven : String × Sys.Pred Vars :=
  ("count ≠ -7", smt! state => state.count! ≠ (- 7))

def sys (cex : Bool) : Sys Vars where
  logic := .qf_lia
  svars := vars
  init := init
  trans := trans
  candidates :=
    if cex then #[count_ne_minus_seven]
    else #[count_pos, count_ne_minus_seven]

def showModel (model : Sys.Model Vars) (pref := "") : IO Unit := do
  println! "  {pref}    reset = {model.reset!}"
  println! "  {pref}startStop = {model.startStop!}"
  println! "  {pref} counting = {model.counting!}"
  println! "  {pref}    count = {model.count!}"

def checkInit (sys : Sys Vars) : SmtIO Unit := do
  println! "checking stopwatch init"
  if let some cex ← sys.checkInit then
    println! "cex:"
    sw.showModel cex
  else
    println! "candidates hold in init"

def checkTrans (sys : Sys Vars) : SmtIO Unit := do
  println! "checking stopwatch trans"
  if let some (prev, curr) ← sys.checkTrans then
    println! "cex:"
    sw.showModel curr "curr | "
    println! "  ------------------------"
    sw.showModel prev "prev | "
  else
    println! "candidates hold in trans"

end sw



/-- info:
checking stopwatch init
candidates hold in init
-/
#test sw.sys false |> sw.checkInit

/-- info:
checking stopwatch trans
candidates hold in trans
-/
#test sw.sys false |> sw.checkTrans

/-- info:
checking stopwatch init
candidates hold in init
-/
#test sw.sys true |> sw.checkInit

/-- info:
checking stopwatch trans
cex:
  curr |     reset = false
  curr | startStop = false
  curr |  counting = true
  curr |     count = -7
  ------------------------
  prev |     reset = false
  prev | startStop = false
  prev |  counting = true
  prev |     count = -8
-/
#test sw.sys true |> sw.checkTrans
