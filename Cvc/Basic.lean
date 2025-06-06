/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Batteries.Data.Rat.Basic
import Batteries.Data.RBMap

import cvc5



/-! # Library setup: re-exports and helpers -/
namespace Cvc



/-- The constant combinator. -/
abbrev 𝕂 (val : α) (_ : β) : α := val


abbrev RBMap (α β : Type) [Ord α] :=
  Batteries.RBMap α β compare

namespace RBMap variable [Ord α]

open Batteries renaming RBMap → Map

/-- The empty map. -/
def empty : RBMap α β := Map.empty

/-- Removes from `map` the bindings `key`/`val` such that `¬ f key val`. -/
def filter : (map : RBMap α β) → (f : α → β → Bool) → RBMap α β :=
  Map.filter

/-- Removes from `map` the bindings `key`/`val` such that `¬ f val`. -/
def filterVal (map : RBMap α β) (f : β → Bool) : RBMap α β :=
  map.filter fun _ => f

/-- Inserts a `key`/`val` binding in a map.

See also `RBMap.insert'`.
-/
def insert : (map : RBMap α β) → (key : α) → (val : β) → RBMap α β :=
  Map.insert

/-- Adds a `key`/`val` binding in a map, returns the previous value of `key` if any.

See also `RBMap.insert`.
-/
def insert' (map : RBMap α β) (key : α) (val : β) : (Option β) × RBMap α β :=
  (map.find? key, map.insert key val)

/-- Adds a `key`/`val` binding in a map, `none` if a binding for `key` already exists. -/
def insertNew? (map : RBMap α β) (key : α) (val : β) : Option (RBMap α β) :=
  let (prev?, map) := map.insert' key val
  prev?.map (𝕂 map)

/-- Removes from `map` the binding for `key`, if any.

See also `RBMap.erase'`.
-/
def erase : (map : RBMap α β) → (key : α) → RBMap α β :=
  Map.erase

/-- Removes a `key`/`val` binding from a map, yields `some val` if such a binding existed.

See also `RBMap.erase`.
-/
def erase' (map : RBMap α β) (key : α) : (Option β) × RBMap α β :=
  (map.find? key, map.erase key)

/-- Removes a `key`/`val` binding from a map, `none` if no binding for `key` existed. -/
def eraseExisting? (map : RBMap α β) (key : α) : Option (RBMap α β) :=
  match map.erase' key with
  | (some _, map) => map
  | (none, _) => none

/-- Map over the values of a map. -/
def mapVal : (f : α → β → γ) → (map : RBMap α β) → RBMap α γ :=
  Map.mapVal

/-- Monadic filter/map over the values of a map. -/
def filterMapValM [Monad m] (f : α → β → m (Option γ)) (map : RBMap α β) : m (RBMap α γ) :=
  RBMap.empty |> map.foldlM fun map key val => do
    if let some val ← f key val then return map.insert key val else return map

/-- Monadic map over the values of a map. -/
def mapValM [Monad m] (f : α → β → m γ) (map : RBMap α β) : m (RBMap α γ) :=
  map.filterMapValM (some <$> f · ·)

/-- Filter/map over the values of a map. -/
def filterMapVal (f : α → β → Option γ) (map : RBMap α β) : RBMap α γ :=
  map.filterMapValM (m := Id) f

/-- Monadic filter/map over the values of a map into an array of values. -/
def filterMapValToArrayM [Monad m] (f : α → β → m (Option γ)) (map : RBMap α β) : m (Array γ) :=
  #[] |> map.foldlM fun array key val => do
    if let some val ← f key val then return array.push val else return array

/-- Filter/map over the values of a map into an array of values. -/
def filterMapValToArray (f : α → β → Option γ) (map : RBMap α β) : Array γ :=
  map.filterMapValToArrayM (m := Id) f

/-- Monadic map over the values of a map into an array of values. -/
def mapValToArrayM [Monad m] (f : α → β → m γ) (map : RBMap α β) : m (Array γ) :=
  map.filterMapValToArrayM (some <$> f · ·)

/-- Map over the values of a map into an array of values. -/
def mapValToArray (f : α → β → γ) (map : RBMap α β) : Array γ :=
  map.mapValToArrayM (m := Id) f

/-- Monadic key-ignoring map over the values of a map. -/
def mapOnlyValM [Monad m] (f : β → m γ) (map : RBMap α β) : m (RBMap α γ) :=
  map.mapValM fun _ => f

/-- Key-ignoring map over the values of a map. -/
def mapOnlyVal (f : β → γ) (map : RBMap α β) : RBMap α γ :=
  map.mapVal fun _ => f

/-- Key-ignoring monadic filter/map over the values of a map. -/
def filterMapOnlyValM [Monad m] (f : β → m (Option γ)) (map : RBMap α β) : m (RBMap α γ) :=
  map.filterMapValM fun _ => f

/-- Key-ignoring filter/map over the values of a map. -/
def filterMapOnlyVal (f : β → Option γ) (map : RBMap α β) : RBMap α γ :=
  map.filterMapOnlyValM (m := Id) f

/-- Key-ignoring filter/map over the values of a map into an array of values. -/
def filterMapOnlyValToArrayM [Monad m] (f : β → m (Option γ)) (map : RBMap α β) : m (Array γ) :=
  map.filterMapValToArrayM fun _ => f

/-- Key-ignoring filter/map over the values of a map into an array of values. -/
def filterMapOnlyValToArray (f : β → Option γ) (map : RBMap α β) : Array γ :=
  map.filterMapOnlyValToArrayM (m := Id) f

/-- Key-ignoring monadic map over the values of a map into an array of values. -/
def mapOnlyValToArrayM [Monad m] (f : β → m γ) (map : RBMap α β) : m (Array γ) :=
  map.mapValToArrayM fun _ => f

/-- Key-ignoring map over the values of a map into an array of values. -/
def mapOnlyValToArray (f : β → γ) (map : RBMap α β) : Array γ :=
  map.mapOnlyValToArrayM (m := Id) f

def filterMapFoldM {Acc : Type} [Monad m] (init : Acc)
  (f : Acc → α → β → m (Acc × Option γ))
  (map : RBMap α β)
: m (Acc × RBMap α γ) := do
  let mut map' : RBMap α γ := .empty
  let mut acc := init
  for (key, val) in map do
    let (acc', val?) ← f acc key val
    acc := acc'
    if let some val := val? then
      map' := map'.insert key val
  return (acc, map')


end RBMap



abbrev RBSet (α : Type) [Ord α] :=
  Batteries.RBSet α compare

namespace RBSet variable [Ord α]

open Batteries renaming RBSet → Set

/-- The empty set. -/
def empty : RBSet α := Set.empty

/-- Removes from `set` the elements `elm` for which `¬ f elm`. -/
def filter : (set : RBSet α) → (f : α → Bool) → RBSet α :=
  Set.filter

/-- Inserts an element in the set.

See also `RBSet.insert'`.
-/
def insert : (set : RBSet α) → α → RBSet α :=
  Set.insert

/-- Inserts an element in the set, yields `true` *iff* the element is new.

See also `RBSet.insert`.
-/
def insert' (set : RBSet α) (elm : α) : Bool × RBSet α :=
  (set.contains elm, set.insert elm)

/-- Removes an element from a set.

See also `RBSet.erase'`.
-/
def erase (set : RBSet α) (k : α) : RBSet α := Set.erase set (compare k)

/-- Removes an element from a set, yields `true` *iff* the element was there.

See also `RBSet.erase`
-/
def erase' (set : RBSet α) (elm : α) : Bool × RBSet α :=
  (set.contains elm, set.insert elm)

end RBSet



def Decidable.conj {p q : Prop} [Decidable p] [Decidable q] : Decidable (p ∧ q) :=
  inferInstance

def Decidable.conj' {p q : Prop} (ip : Decidable p) (iq : Decidable q) : Decidable (p ∧ q) :=
  inferInstance



scoped
syntax:max "ls!" interpolatedStr(term) : term
macro_rules
| `(ls! $interpSrt) => `( (fun () => s!$interpSrt : Unit → String)  )



export _root_ (Rat)



/-- A check-sat result.-/
inductive CheckSat
/-- Formulas asserted are satisfiable, *i.e.* a model exists. -/
| sat
/-- Formulas are unsatisfiable, no assignment of the symbols makes them true. -/
| unsat
/-- Solver returned unknown. -/
| unknown (desc : String)
/-- Solver returned some unexpected result. -/
| other (desc : String)

namespace CheckSat

/-- Conversion to a simple *is sat?* flag, `none` on unknown/unexpected results. -/
def isSat? : CheckSat → Option Bool
| sat => true
| unsat => false
| unknown _ | other _ => none

end CheckSat



inductive Error : Type
| internal (msg : String)
| unsupported (msg : String)
| userError (msg : String)
deriving Inhabited


namespace Error

/-- Used to allow `String` and `Unit → String` as context messages. -/
class AsString (α : Type) : Type where
  /-- Conversion to strings. -/
  asString : α → String

instance : AsString String := ⟨id⟩
instance : AsString (Unit → String) := ⟨fun f => f ()⟩

def mapMsg (f : String → String) : Error → Error
| .internal msg => f msg |> .internal
| .unsupported msg => f msg |> .unsupported
| .userError msg => f msg |> .userError

def append (self : Error) (txt : String) (newline := true) : Error :=
  let txt := if newline then "\n"++txt else txt
  self.mapMsg (· ++ txt)


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

section variable [Monad m] [MonadExcept Error m] (msg : String)

/-- Throws an `Error.userError`. -/
protected def throwUser : m α := do
  throw <| Error.userError msg

/-- Throws an `Error.internal`. -/
protected def throwInternal : m α := do
  throw <| Error.internal msg

/-- Throws an `Error.internal` about unreachable code. -/
protected def throwUnreachable (msg : String := "") : m α := do
  let sep := if msg.isEmpty then "" else ": "
  throw <| Error.internal s!"reached unreachable code{sep}{msg}"

end

end Error

export Error (throwUser throwInternal throwUnreachable)



/-- Alias for `Except Error`. -/
abbrev Res := Except Error

namespace Res
@[inherit_doc Except.ok]
abbrev ok : α → Res α := Except.ok
@[inherit_doc Except.error]
abbrev error : Error → Res α := Except.error

instance : MonadLift (Except cvc5.Error) Res :=
  ⟨fun | .ok v => .ok v | .error e => .error (Error.ofCvc5 e)⟩

instance : MonadLift (Except cvc5.Error) Res.{0} :=
  ⟨fun | .ok v => .ok v | .error e => .error (Error.ofCvc5 e)⟩

def fail (e : Error) : Res α :=
  .error e
def failInternal (e : String) : Res α :=
  Except.error.{0} <| .internal e
def failUser (e : String) : Res α :=
  Except.error.{0} <| .userError e
def failTodo (e : String) : Res α :=
  Except.error.{0} <| .unsupported e

def context [A : Error.AsString S] (s : S) : Res α → Res α
| .ok val => .ok val
| .error e => .error <| e.mapMsg (s!"{·}\n{A.asString s}")

def lift : Except cvc5.Error α → Res α := liftM

def up1 {α : Type} : (res : Res α) → Res.{1} (ULift α)
| .ok a => .ok (.up a) | .error e => .error e

def lift1 {α : Type} : Except.{0} cvc5.Error α → Res.{1} (ULift α) :=
  up1 ∘ lift

end Res


/-! ## Helpers -/



structure ArrayMin (n : Nat) (α : Type u) : Type u where
mk' ::
  pref : Array α
  inv : pref.size = n := by rfl
  suff : Array α := #[]
deriving Hashable

namespace ArrayMin

instance [Inhabited α] : Inhabited (ArrayMin n α) where
  default := ⟨Array.replicate n default, by simp, #[]⟩

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
    have := self.pref_size ▸ h
    self.pref[i]
  else
    have : i - n < self.suff.size := by
      simp only [size] at h_i
      exact Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt h) h_i
    self.suff[i - n]

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
  have := self.pref_size ▸ h
  self.pref[i]

def toArray : Array α := self.pref ++ self.suff

def toList : List α := self.pref.toList ++ self.suff.toList

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
