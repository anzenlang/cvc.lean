import Cvc.Safe



namespace Cvc.Safe



namespace Symbols

inductive Unrolling (State : Symbols S) (F : Nat → Type u) : Nat → Type u
| empty : Unrolling State F 0
| cons (data : F n) (tail : Unrolling State F n) : Unrolling State F n.succ

namespace Unrolling

def reverse.loop
  {State : Symbols S}
  (acc : State.Unrolling (𝕂 α) (k - i))
  (u : State.Unrolling (𝕂 α) i)
  (h : i ≤ k := by first | simp | omega)
: State.Unrolling (𝕂 α) k := by
  cases i with
  | zero => exact acc
  | succ i' =>
    let .cons data tail := u
    let data : 𝕂 α (k - (i' + 1)) := data
    let acc := Unrolling.cons data acc
    let h_sub : k - i' ≠ 0 :=
      Nat.sub_ne_zero_of_lt (Nat.lt_of_succ_le h)
    simp [
      Nat.sub_add_eq, Nat.add_one_sub_one,
      Nat.sub_one_add_one h_sub
    ] at acc
    exact loop (i := i') acc tail

def reverse {α : Type u} {State : Symbols S}
: State.Unrolling (𝕂 α) k → State.Unrolling (𝕂 α) k :=
  reverse.loop ((Nat.sub_self k).symm ▸ .empty)

def get : {k : Nat} → (i : Fin k) → Unrolling State F k → F i
| 0, ⟨_, _⟩, _ => by contradiction
| k + 1, ⟨i, i_lt_k⟩, .cons data tail =>
  if i_eq_k : i = k
  then i_eq_k ▸ data
  else tail.get ⟨i, by omega⟩

def mapM.loop [Monad m]
  (f : (i : Fin k) → F i → m (F' i))
: (i : Fin k)
→ (data : F i)
→ (tail : Unrolling State F i)
→ m (Unrolling State F' i.succ)
| ⟨0, h⟩, data, .empty => do
  let data ← f ⟨0, h⟩ data
  return Unrolling.empty.cons data
| ⟨i + 1, h_iAdd1⟩, data, .cons nextData nextTail => do
  let data ← f ⟨i + 1, h_iAdd1⟩ data
  let tail ← loop f ⟨i, by omega⟩ nextData nextTail
  return tail.cons data

def mapM
  [Monad m]
  (f : (i : Fin k) → F i → m (F' i))
  (u : Unrolling State F k)
: m (Unrolling State F' k) := by
  cases k with
  | zero => exact return .empty
  | succ i =>
    cases u with
    | cons data tail => exact mapM.loop f ⟨i, by omega⟩ data tail

def map
  (f : (i : Fin k) → F i → F' i)
  (u : Unrolling State F k)
: Unrolling State F' k :=
  u.mapM (m := Id) (return f · ·)

def forIn.loop [Monad m]
  (f : ((i : Fin k) × F i) → β → m (ForInStep β))
  (acc : β)
: (i : Fin k)
→ (data : F i)
→ (tail : Unrolling State F i)
→ m β
| ⟨0, h⟩, data, .empty => do
  match ← f ⟨⟨0, h⟩, data⟩ acc with
  | .done res | .yield res => return res
| ⟨i + 1, h_iAdd1⟩, data, .cons nextData nextTail => do
  match ← f ⟨⟨i + 1, h_iAdd1⟩, data⟩ acc with
  | .done res => return res
  | .yield acc => loop f acc ⟨i, by omega⟩ nextData nextTail

protected def forIn [Monad m]
  (u : Unrolling State F k)
  (init : β)
  (f : ((i : Fin k) × F i) → β → m (ForInStep β ))
: m β := by
  cases k with
  | zero => exact return init
  | succ k => cases u with
    | cons data tail => exact forIn.loop f init ⟨k, by omega⟩ data tail

instance [Monad m] : ForIn m (Unrolling State F k) ((i : Fin k) × F i) :=
  ⟨Unrolling.forIn⟩

def foldM
  [Monad m]
  (f : (acc : β) → (i : Fin k) → (data : F i) → m β)
  (init : β)
  (u : Unrolling State F k)
: m β := do
  let mut acc := init
  for ⟨i, data⟩ in u do
    acc ← f acc i data
  return acc

def fold : (β → (i : Fin k) → F i → β) → β → Unrolling State F k → β :=
  foldM (m := Id)

end Unrolling

end Symbols



protected structure TSys.Unrolled (step : Nat) (α : Type u) where
  data : α

namespace Symbols

-- variable [Monad m]

-- structure Model (S) [Symbols S] (step : Nat) extends TSys.Unrolled step (S Id)
-- where protected mkRaw ::

-- def Model.mk [Symbols S] : S Id → Model S step :=
--   Model.mkRaw ∘ Unrolled.mk

-- structure BVars (S) [Symbols S] (step : Nat) extends TSys.Unrolled step (S BVar)
-- where protected mkRaw ::

-- def BVars.mk [Symbols S] : S BVar → BVars S step :=
--   BVars.mkRaw ∘ Unrolled.mk

-- structure Terms (S) [Symbols S] (step : Nat) extends TSys.Unrolled step (S Term)
-- where protected mkRaw ::
-- def Terms.mk [Symbols S] : S Term → Terms S step :=
--   Terms.mkRaw ∘ Unrolled.mk



-- def declare [State : Symbols S] (symbols : State.Symbols) (k : Nat) : SmtM (State.Terms k) :=
--   Terms.mk <$> State.mapM symbols fun symbol => symbol.declare k

-- def bvars [State : Symbols S] (symbols : State.Symbols) (k : Nat) : SmtM (State.BVars k) :=
--   BVars.mk <$> State.mapM symbols fun symbol => symbol.bvar k

-- def bvarsList [State : Symbols S] (bvars : State.BVars k) : SmtM Safe.BVars := do
--   let mut list := Safe.BVars.empty
--   for ⟨_, _, bvar⟩ in bvars.data do
--     list := list.push bvar
--   return list

-- def getModel [State : Symbols S] (terms : State.Terms k) : Smt.SatM (State.Model k) :=
--   Model.mk <$> State.mapM terms.data fun term => term.getVal

abbrev Model {S} [State : Symbols S] : (step : Nat) → Type := fun _ => State.Concrete

abbrev Trace (State : Symbols S) (k : Nat) :=
  State.Unrolling State.Model k

namespace Trace

protected
def toString (symbols : State.Idents)
: {k : Nat} → (cex : Trace State k) → (pref : String := "") → (acc : String := "") → String
| 0, .empty, pref, acc => s!"{pref}‼️ empty counterexample ‼️{accAsSep acc}"
| 1, .cons state .empty, pref, acc => present acc pref state 0
| k + 1, .cons state tail, pref, acc =>
  present acc pref state k
  |> Trace.toString symbols tail pref
where
  getSymbol (k : Nat) := Id.run do
    let mut count := 0
    for s in symbols do
      if count = k
      then return s.snd.get
      else count := count + 1
    return "<unknown state variable>"
  accAsSep : String → String
  | "" => ""
  | s => s ++ "\n"
  present acc pref (state : State.Model _) k := Id.run do
    let mut s := s!"{accAsSep acc}{pref}|===| state {k}"
    let mut count := 0
    for ⟨_, val⟩ in state do
      let _ := val.inst
      s := s!"{s}\n{pref}| {getSymbol count} = {val.get}"
      count := count + 1
    return if k = 0 then s!"{s}\n{pref}|===|" else s

end Trace

end Symbols
