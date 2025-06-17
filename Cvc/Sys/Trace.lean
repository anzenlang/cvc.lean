/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.State.Defs



namespace Cvc



namespace Symbols

/-- A trace of `length` indexed data.

Roughly equivalent to a list of indexed data with decreasing indices (`length - 1` to `0`). Note
that this means the data of index `0` (if any) is always the very *last* element in the trace.
-/
inductive Trace (State : Symbols Struct) (Repr : Nat → Type) : (length : Nat) → Type
/-- The empty trace. -/
| empty : Trace State Repr 0
/-- Some data with index `n` and the tail of the trace. -/
| cons (data : Repr n) (tail : Trace State Repr n) : Trace State Repr n.succ

/-- A trace of terms. -/
abbrev TermTrace (State : Symbols Struct) (length : Nat) :=
  State.Trace State.TermsAt length

/-- A trace of values. -/
abbrev ValueTrace (State : Symbols Struct) (length : Nat) :=
  State.Trace State.ValuesAt length

namespace Trace

/-- Builds a trace of length `1`. -/
def mkOne [State : Symbols Struct] {Repr : Nat → Type} : (data : Repr 0) → State.Trace Repr 1 :=
  empty.cons

/-- Retrieves a state in a trace from its index. -/
def get : {k : Nat} → Trace S R k → (idx : Nat)
→ (in_range : idx < k := by (try simp [*]) <;> omega) → R idx
| 0, _, _, _ => by contradiction
| k + 1, .cons data tail, i, i_lt_k => if i_eq_k : i = k then i_eq_k ▸ data else tail.get i

@[inherit_doc get]
def get? (trace : Trace S R k) (idx : Nat) : Option (R idx) :=
  if _ : idx < k then trace.get idx else none

/-- Deconstructs a non-empty trace. -/
def decons {k : Nat} : Trace S R (k + 1) → R k × Trace S R k
| .cons data tail => (data, tail)

/-- Data at index `k`. -/
def getData (trace : Trace S R (k + 1)) : R k := trace.decons.fst
/-- Tail of a non-empty trace. -/
def getTail (trace : Trace S R (k + 1)) : Trace S R k := trace.decons.snd

/-- Alias for a reversed `Trace`, used to change the .

Actually a normal `Trace`, but `Repr` is manipulated so that the `Repr`-data at index `idx` is
actually `Repr (k - idx - 1)`. As a result `Repr 0` is always the *first* element in the trace,
as opposed to a regular `Trace`.

`Rev` traces should not be used in `Trace.cons`: the first data having index `0` we can only put
data of index `0` in front of it, which does not make sense.

# TODO

- make opaque or handle differently?
-/
protected abbrev Rev (State : Symbols Struct) (Repr : Nat → Type) (k : Nat) : Type :=
  State.Trace (fun idx => Repr (k - idx - 1)) k

/-- Auxiliary function for reversing trace, *tail-recursive*. -/
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



variable [Monad m]

/-- Auxiliary function for `Trace.mapM`. -/
def mapM.loop (f : (i : Fin k) → R i → m (R' i))
: (i : Fin k) → (data : R i) → (tail : Trace State R i) → m (Trace S R' i.succ)
| ⟨0, h⟩, data, .empty => do
  let data ← f ⟨0, h⟩ data
  return Trace.empty.cons data
| ⟨i + 1, in_range_i_succ⟩, data, .cons nextData nextTail => do
  let data ← f ⟨i + 1, in_range_i_succ⟩ data
  let tail ← loop f ⟨i, by omega⟩ nextData nextTail
  return tail.cons data

/-- Monadic map over trace data. -/
def mapM (trace : Trace S R k)
  (f : (i : Fin k) → R i → m (R' i))
: m (Trace S R' k) := by
  cases k with
  | zero => exact return .empty
  | succ i =>
    let (data, tail) := trace.decons
    exact mapM.loop f ⟨i, by omega⟩ data tail

/-- Map over trace data. -/
def map (trace : Trace S R k) (f : (i : Fin k) → R i → R' i) : Trace S R' k :=
  trace.mapM (m := Id) f

/-- Auxiliary function for `Trace.forIn`. -/
protected def forIn.loop
  (f : ((i : Fin k) × R i) → β → m (ForInStep β)) (acc : β)
: (i : Fin k) → (data : R i) → (tail : Trace S R i) → m β
| ⟨0, h⟩, data, .empty => do
  match ← f ⟨⟨0, h⟩, data⟩ acc with
  | .done res | .yield res => return res
| ⟨i + 1, in_range_i_succ⟩, data, .cons nextData nextTail => do
  match ← f ⟨⟨i + 1, in_range_i_succ⟩, data⟩ acc with
  | .done res => return res
  | .yield acc => forIn.loop f acc ⟨i, by omega⟩ nextData nextTail

/-- Used to instantiate `ForIn`. -/
protected def forIn (trace : Trace S R k) (init : β)
  (f : ((i : Fin k) × R i) → β → m (ForInStep β))
: m β := by
  cases k with
  | zero => exact return init
  | succ k =>
    let (data, tail) := trace.decons
    exact forIn.loop f init ⟨k, by omega⟩ data tail

instance : ForIn m (Trace State R k) ((i : Fin k) × R i) :=
  ⟨Trace.forIn⟩



section foldM variable (trace : Trace State R k) (f : β → (i : Fin k) → R i → m β) (init : β)

/-- Monadic fold over trace elements with *decreasing* indices. -/
def foldDecM : m β := do
  let mut acc := init
  for ⟨i, data⟩ in trace do
    acc ← f acc i data
  return acc

/-- Monadic fold over trace elements with *increasing* indices. -/
def foldIncM : m β := do
  trace.reverse.foldDecM (init := init) fun acc i => f acc ⟨k - i - 1, by omega⟩

section fold variable (f : β → (i : Fin k) → R i → β) (init : β)

/-- Fold over trace elements with *decreasing* indices. -/
def foldDec : β := foldDecM (m := Id) trace f init

/-- Fold over trace elements with *increasing* indices. -/
def foldInc : β := trace.foldIncM (m := Id) f init

end fold

end foldM

end Trace

end Symbols
