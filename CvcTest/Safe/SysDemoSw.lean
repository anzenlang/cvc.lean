/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import CvcTest.Safe.Init
import CvcTest.Safe.Sys



namespace Cvc.Safe.Test

open Sys (SVar SVars)

namespace sw

structure Vars (F : Type → Type) where
  reset : SVar F Bool
  startStop : SVar F Bool
  counting : SVar F Bool
  count : SVar F Int

namespace Vars
variable (self : Vars F)

def untype : SVars.Untyped F := #[
  self.reset.untype,
  self.startStop.untype,
  self.counting.untype,
  self.count.untype
]

def reset! := self.reset.val
def startStop! := self.startStop.val
def counting! := self.counting.val
def count! := self.count.val

instance instSVars : SVars Vars where
  allDoM self f := do
    let reset ← self.reset.mapM f
    let startStop ← self.startStop.mapM f
    let counting ← self.counting.mapM f
    let count ← self.count.mapM f
    return ⟨reset, startStop, counting, count⟩
  forIn self := self.untype.forIn
end Vars

def vars : Vars (𝕂 String) where
  reset := SVar.mk "reset"
  startStop := SVar.mk "startStop"
  counting := SVar.mk "counting"
  count := SVar.mk "count"

def init : Sys.PredT IO Vars := smt! fun state =>
  (state.count! = 0) ∧ (state.counting! = state.startStop!)

def trans : Sys.PredT2 IO Vars := smt! fun prev curr =>
  let counting ←
    curr.counting! = if curr.startStop! then ¬ prev.counting! else prev.counting!;
  let countDef ←
    if curr.reset! then 0
    else prev.count! + (if prev.counting! then 1 else 0);
  let count ←
    curr.count! = countDef;
  counting ∧ count

def count_pos : String × Sys.Pred Vars :=
  ("0 ≤ count", smt! fun state => state.count! ≥ 0)

def count_ne_minus_seven : String × Sys.Pred Vars :=
  ("count ≠ -7", smt! fun state => state.count! ≠ - 7)

def sys (cex : Bool) : SysT IO Vars where
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

def checkInit [Monad m] [MonadLiftT IO m] (sys : SysT m Vars) : SmtT m Unit := do
  println! "checking stopwatch init"
  if let some cex ← sys.checkInit then
    println! "cex:"
    sw.showModel cex
  else
    println! "candidates hold in init"

def checkTrans [Monad m] [MonadLiftT IO m] (sys : SysT m Vars) : SmtT m Unit := do
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
#test do
  let sys := sw.sys false
  sw.checkInit sys

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

/-- info:
computing the preimage of the *bad states* for
- count ≠ -7
→ (and counting (= count (- 8)))
-/
#test do
  let sys := sw.sys true
  println! "computing the preimage of the *bad states* for"
  for (name, _) in sys.candidates do
    println! "- {name}"
  let preimage ← sys.preimageOfBad
  println! "→ {preimage}"

/-- info:
computing the preimage of the *bad states* for
- 0 ≤ count
- count ≠ -7
→ false
-/
#test do
  let sys := sw.sys false
  println! "computing the preimage of the *bad states* for"
  for (name, _) in sys.candidates do
    println! "- {name}"
  let preimage ← sys.preimageOfBad
  println! "→ {preimage}"
