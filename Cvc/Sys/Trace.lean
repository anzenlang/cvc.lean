/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.State.Defs



namespace Cvc



namespace Symbols

inductive Trace (State : Symbols Struct) (Repr : Nat → Type) : (length : Nat) → Type
| empty : Trace State Repr 0
| cons (data : Repr n) (tail : Trace State Repr n) : Trace State Repr n.succ

abbrev TermTrace (State : Symbols Struct) (length : Nat) :=
  State.Trace State.TermsAt length

abbrev ValueTrace (State : Symbols Struct) (length : Nat) :=
  State.Trace State.ValuesAt length

namespace Trace

def mkOne [State : Symbols Struct] {Repr : Nat → Type} : (data : Repr 0) → State.Trace Repr 1 :=
  empty.cons

def get' : {k : Nat} → (idx : Nat) → (in_range : idx < k) → Trace S R k → R idx
  | 0, _, _, _ => by contradiction
  | k + 1, i, i_lt_k, .cons data tail =>
    if i_eq_k : i = k then i_eq_k ▸ data else tail.get' i (by omega)

section variable (trace : Trace S R k) (idx : Nat)

def get (in_range : idx < k := by (try simp [*]) <;> omega) : R idx :=
  trace.get' idx in_range

def get? : Option (R idx) := if in_range : idx < k then trace.get idx in_range else none

end

def decons {k : Nat} : Trace S R (k + 1) → R k × Trace S R k
| .cons data tail => (data, tail)

def getData (trace : Trace S R (k + 1)) : R k := trace.decons.fst
def getTail (trace : Trace S R (k + 1)) : Trace S R k := trace.decons.snd

protected abbrev Rev (State : Symbols Struct) (Repr : Nat → Type) (k : Nat) : Type :=
  State.Trace (fun idx => Repr (k - idx - 1)) k

def reverse.loop
  [State : Symbols Struct]
  (k i : Nat)
  (trace : State.Trace R i)
  (acc : Trace State (fun idx => R (k - idx - 1)) (k - i))
  (h_i : i ≤ k := by (try simp [*]) <;> omega)
: Trace.Rev State R k := by
  cases i with
  | zero => exact acc
  | succ i' =>
    let (data, tail) := trace.decons
    let cons := acc.cons
    let h_sub : k - i' ≠ 0 :=
      Nat.sub_ne_zero_of_lt (Nat.lt_of_succ_le h_i)
    let h_red : k - (k - i' - 1) - 1 = i' := by omega
    simp only [Nat.sub_add_eq, Nat.succ_eq_add_one, Nat.sub_one_add_one h_sub, h_red] at cons
    let acc' := cons data
    exact loop k i' tail acc'

/-- Reverses a trace, *tail-recursive*. -/
def reverse [State : Symbols Struct] (trace : State.Trace R k) : Trace.Rev State R k :=
  reverse.loop k k trace (by simp only [Nat.sub_self] ; exact .empty)

@[inherit_doc reverse]
abbrev rev := @reverse


def mapM.loop [Monad m] (f : (i : Fin k) → R i → m (R' i))
: (i : Fin k) → (data : R i) → (tail : Trace State R i) → m (Trace S R' i.succ)
| ⟨0, h⟩, data, .empty => do
  let data ← f ⟨0, h⟩ data
  return Trace.empty.cons data
| ⟨i + 1, in_range_i_succ⟩, data, .cons nextData nextTail => do
  let data ← f ⟨i + 1, in_range_i_succ⟩ data
  let tail ← loop f ⟨i, by omega⟩ nextData nextTail
  return tail.cons data

def mapM [Monad m] (trace : Trace S R k)
  (f : (i : Fin k) → R i → m (R' i))
: m (Trace S R' k) := by
  cases k with
  | zero => exact return .empty
  | succ i =>
    let (data, tail) := trace.decons
    exact mapM.loop f ⟨i, by omega⟩ data tail

def map (trace : Trace S R k) (f : (i : Fin k) → R i → R' i) : Trace S R' k :=
  trace.mapM (m := Id) f

protected def forIn.loop [Monad m]
  (f : ((i : Fin k) × R i) → β → m (ForInStep β)) (acc : β)
: (i : Fin k) → (data : R i) → (tail : Trace S R i) → m β
| ⟨0, h⟩, data, .empty => do
  match ← f ⟨⟨0, h⟩, data⟩ acc with
  | .done res | .yield res => return res
| ⟨i + 1, in_range_i_succ⟩, data, .cons nextData nextTail => do
  match ← f ⟨⟨i + 1, in_range_i_succ⟩, data⟩ acc with
  | .done res => return res
  | .yield acc => forIn.loop f acc ⟨i, by omega⟩ nextData nextTail

protected def forIn [Monad m] (trace : Trace S R k) (init : β)
  (f : ((i : Fin k) × R i) → β → m (ForInStep β))
: m β := by
  cases k with
  | zero => exact return init
  | succ k =>
    let (data, tail) := trace.decons
    exact forIn.loop f init ⟨k, by omega⟩ data tail

instance [Monad m] : ForIn m (Trace State R k) ((i : Fin k) × R i) :=
  ⟨Trace.forIn⟩



/-- Monadic fold over trace elements with *decreasing* indices.

**NB:** folds from `R (k - 1)` to `R 0`, see also `Trace.revFoldM`.
-/
def foldM [Monad m] (trace : Trace State R k)
  (f : (acc : β) → (i : Fin k) → (data : R i) → m β) (init : β)
: m β := do
  let mut acc := init
  for ⟨i, data⟩ in trace do
    acc ← f acc i data
  return acc

/-- Fold over trace elements with *decreasing* indices.

**NB:** folds from `R (k - 1)` to `R 0`, see also `Trace.revFold`.
-/
def fold (trace : Trace State R k) (f : β → (i : Fin k) → R i → β) (init : β) : β :=
  foldM (m := Id) trace f init

/-- Monadic fold over trace elements with *increasing* indices.

Effectively the same as `trace.reverse.foldM f' init` where `f'` is a type-massaged version of `f`.

**NB:** folds from `R 0` to `R (k - 1)`, see also `Trace.foldM`.
-/
def revFoldM [Monad m] (trace : Trace State R k)
  (f : (i : Fin k) → (data : R i) → (acc : β) → m β) (init : β)
: m β := do
  trace.reverse.foldM (init := init) fun acc i data => f ⟨k - i - 1, by omega⟩ data acc

/-- Fold over trace elements with *increasing* indices.

Effectively the same as `trace.reverse.fold f' init` where `f'` is a type-massaged version of `f`.

**NB:** folds from `R 0` to `R (k - 1s)`, see also `Trace.fold`.
-/
def revFold (trace : Trace State R k)
  (f : (i : Fin k) → (date : R i) → (acc : β) → β) (init : β)
: β :=
  trace.revFoldM (m := Id) f init

end Trace

end Symbols
