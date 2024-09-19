/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import cvc5



/-! # Library setup: re-exports and helpers -/
namespace Cvc



export Lean (Rat)




/-! ## Re-exports from `cvc5` -/

inductive Error : Type u
| internal (msg : String)
| unsupported (msg : String)
| userError (msg : String)
deriving Inhabited

namespace Error

def toCvc5 : Error → cvc5.Error
| .internal "a value is missing" => .missingValue
| .internal msg => .error msg
| .unsupported msg => .unsupported msg
| .userError msg => .error msg

def ofCvc5 : cvc5.Error → Error
| .missingValue => .internal "a value is missing"
| .error msg => .internal s!"{msg}"
| .option msg => .internal s!"option error: {msg}"
| .unsupported msg => .unsupported msg
| .recoverable msg => .internal s!"recoverable: {msg}"

instance : MonadLift (Except cvc5.Error) (Except Error) where
  monadLift
  | .ok res => .ok res
  | .error e => .error (ofCvc5 e)

instance : Coe cvc5.Error Error := ⟨ofCvc5⟩

protected def toString : Error → String
| .internal msg => "internal error: " ++ msg
| .unsupported msg => "unsupported: " ++ msg
| .userError msg => "user error: " ++ msg

instance instToString : ToString Error :=
  ⟨Error.toString⟩

end Error



/-! ## Helpers -/



structure ArrayMin (n : Nat) (α : Type u) : Type u where
mk' ::
  pref : Array α
  inv : pref.size = n := by rfl
  suff : Array α := #[]
deriving Hashable

namespace ArrayMin

instance [Inhabited α] : Inhabited (ArrayMin n α) where
  default := ⟨Array.mkArray n default, by simp, #[]⟩

def mk (pref : Array α) (suff : Array α := #[]) : ArrayMin pref.size α :=
  ⟨pref, rfl, suff⟩

protected def toString [ToString α] (self : ArrayMin n α) : String :=
  if self.suff.isEmpty then
    toString self.pref
  else
    s!"{self.pref}{self.suff}"

instance [ToString α] : ToString (ArrayMin n α) := ⟨ArrayMin.toString⟩


variable (self : ArrayMin n α)

@[simp]
theorem pref_size : self.pref.size = n :=
  self.inv

abbrev size : Nat := n + self.suff.size

@[simp]
theorem min_le_size : n ≤ self.size := by
  simp only [Nat.le_add_right]

def get : (i : Fin self.size) → α
| ⟨i, h_i⟩ =>
  if h : i < n then
    self.pref.get ⟨i, by simp only [pref_size, h]⟩
  else
    let h' : i - n < self.suff.size := by
      simp [size] at h_i
      exact Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt h) h_i
    self.suff.get ⟨i - n, by simp only [pref_size, h']⟩

instance instGetElem : GetElem (ArrayMin n α) Nat α (fun arr i => i < arr.size) where
  getElem self i h_i := self.get ⟨i, h_i⟩

def get? (self : ArrayMin n α) (i : Nat) : Option α :=
  if h : i < self.size
  then self.get ⟨i, h⟩
  else none

def get! [Inhabited α] (self : ArrayMin n α) (i : Nat) : α :=
  if let some a := self.get? i
  then a
  else panic! s!"illegal index {i} for `ArrayMin {n} _` of size {self.size}"

def getN (i : Nat) (h : i < n := by decide) : α :=
  self.pref.get ⟨i, by simp [h]⟩

def toArray : Array α := self.pref ++ self.suff

def toList : List α := self.pref.data ++ self.suff.data

def push (a : α) : ArrayMin n α :=
  {self with suff := self.suff.push a }

def drainFirst : ArrayMin n.succ α → α × ArrayMin n α
| ⟨⟨fst::pref⟩, h_pref', suff⟩ =>
  (fst, ⟨
    ⟨pref⟩,
    by
      simp at h_pref'
      assumption,
    suff
  ⟩)

instance instForIn : ForIn m (ArrayMin n α) α where
  forIn self init f := do
    let mut acc := init
    for a in self.pref do
      match ← f a acc with
      | .done a => return a
      | .yield a => acc := a
    for a in self.suff do
      match ← f a acc with
      | .done a => return a
      | .yield a => acc := a
    return acc

structure Frame (n : Nat) (α : Type u) : Type u where
private mk ::
  private pref : Array α := #[]
  private suff : Array α := #[]
deriving Inhabited

namespace Frame
def new (n : Nat) : Frame n α :=
  ⟨#[], #[]⟩

variable (self : Frame n α)

def push (a : α) : Frame n α :=
  if self.pref.size < n then
    {self with pref := self.pref.push a}
  else
    {self with suff := self.suff.push a}

def finalize [Inhabited α] : ArrayMin n α :=
  if h : self.pref.size = n then
    ⟨self.pref, h, self.suff⟩
  else
    panic! s!"[ArrayMin.finalize] unexpected prefix of size {self.pref.size}, expected {n}"
end Frame

def newFrame : ArrayMin n α → Frame n β
| _ => Frame.new n

structure Iter (n : Nat) (α : Type u) : Type u where
private mk ::
  val : ArrayMin n α
  pos : Nat

namespace Iter
variable (self : Iter n α)

abbrev isNotDone : Bool :=
  self.pos < self.val.size
abbrev isDone : Bool :=
  ¬ self.isNotDone

def next? : Option α × Iter n α :=
  if h : self.isNotDone then
    let next := self.val.get ⟨
      self.pos,
      by simp [isNotDone] at h ; simp [h]
    ⟩
    (next, {self with pos := self.pos.succ})
  else (none, self)
end Iter

def iter : Iter n α :=
  ⟨self, 0⟩

end ArrayMin
