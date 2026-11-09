/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc

meta import Cvc



/-! # Conversions between the layers

Every type with a counterpart in the other layer converts through `toUntyped` going down and
`toTyped` going up. A sort-indexed type — `Term α`, `BVar α`, `Grammar σ`, a heap, a datatype
handle, a spine — also answers to `erase` going down, and going up has `toTypedAs`, the index
explicit, besides `toTyped`, the index inferred, with `typeCheckAs`/`typeCheck` as aliases. An
unindexed type with both APIs — `Solver`, `Proof` — answers to `relax` going down. Where there is
no way back, only `toUntyped` exists: the heterogeneous lists (`BVars`, `NTs`, datatype `Args`) and
the spines and cases whose sort-erased counterpart is a plain `Terms` or `Term`.

Each signature is pinned here, so that a missing alias, or an index that changed from explicit to
implicit, shows up as a failure.
-/
namespace Cvc.Tests.Conversions

open Cvc

/-- info: @Datatype.Ctor.toTyped : [inst : Ω] → {α : Type} → [ToTyp α] → Datatype.Ctor → Env (Typed.Datatype.Ctor α) -/
#guard_msgs in #check @Cvc.Datatype.Ctor.toTyped

/-- info: @Datatype.Ctor.toTypedAs : [inst : Ω] → (α : Type) → [ToTyp α] → Datatype.Ctor → Env (Typed.Datatype.Ctor α) -/
#guard_msgs in #check @Cvc.Datatype.Ctor.toTypedAs

/-- info: @Datatype.Ctor.typeCheck : [inst : Ω] → {α : Type} → [ToTyp α] → Datatype.Ctor → Env (Typed.Datatype.Ctor α) -/
#guard_msgs in #check @Cvc.Datatype.Ctor.typeCheck

/-- info: @Datatype.Ctor.typeCheckAs : [inst : Ω] → (α : Type) → [ToTyp α] → Datatype.Ctor → Env (Typed.Datatype.Ctor α) -/
#guard_msgs in #check @Cvc.Datatype.Ctor.typeCheckAs

/-- info: @Datatype.Selector.toTyped : [inst : Ω] →
  {α β : Type} → [ToTyp α] → [ToTyp β] → Datatype.Selector → Env (Typed.Datatype.Field α β) -/
#guard_msgs in #check @Cvc.Datatype.Selector.toTyped

/-- info: @Datatype.Selector.toTypedAs : [inst : Ω] →
  (α β : Type) → [ToTyp α] → [ToTyp β] → Datatype.Selector → Env (Typed.Datatype.Field α β) -/
#guard_msgs in #check @Cvc.Datatype.Selector.toTypedAs

/-- info: @Datatype.Selector.typeCheck : [inst : Ω] →
  {α β : Type} → [ToTyp α] → [ToTyp β] → Datatype.Selector → Env (Typed.Datatype.Field α β) -/
#guard_msgs in #check @Cvc.Datatype.Selector.typeCheck

/-- info: @Datatype.Selector.typeCheckAs : [inst : Ω] →
  (α β : Type) → [ToTyp α] → [ToTyp β] → Datatype.Selector → Env (Typed.Datatype.Field α β) -/
#guard_msgs in #check @Cvc.Datatype.Selector.typeCheckAs

/-- info: @Typed.BVar.erase : [inst : Ω] → {α : Type} → Typed.BVar α → Untyped.BVar -/
#guard_msgs in #check @Cvc.Typed.BVar.erase

/-- info: @Typed.BVar.toUntyped : [inst : Ω] → {α : Type} → Typed.BVar α → Untyped.BVar -/
#guard_msgs in #check @Cvc.Typed.BVar.toUntyped

/-- info: @Typed.BVars.erase : [inst : Ω] → Typed.BVars → Untyped.BVars -/
#guard_msgs in #check @Cvc.Typed.BVars.erase

/-- info: @Typed.BVars.toUntyped : [inst : Ω] → Typed.BVars → Untyped.BVars -/
#guard_msgs in #check @Cvc.Typed.BVars.toUntyped

/-- info: @Typed.Datatype.Args.erase : [inst : Ω] → Typed.Datatype.Args → Untyped.Terms -/
#guard_msgs in #check @Cvc.Typed.Datatype.Args.erase

/-- info: @Typed.Datatype.Args.toUntyped : [inst : Ω] → Typed.Datatype.Args → Untyped.Terms -/
#guard_msgs in #check @Cvc.Typed.Datatype.Args.toUntyped

/-- info: @Typed.Datatype.Case.erase : [inst : Ω] → {α β : Type} → Typed.Datatype.Case α β → Untyped.Term -/
#guard_msgs in #check @Cvc.Typed.Datatype.Case.erase

/-- info: @Typed.Datatype.Case.toUntyped : [inst : Ω] → {α β : Type} → Typed.Datatype.Case α β → Untyped.Term -/
#guard_msgs in #check @Cvc.Typed.Datatype.Case.toUntyped

/-- info: @Typed.Datatype.Ctor.erase : [inst : Ω] → {α : Type} → Typed.Datatype.Ctor α → Datatype.Ctor -/
#guard_msgs in #check @Cvc.Typed.Datatype.Ctor.erase

/-- info: @Typed.Datatype.Ctor.toUntyped : [inst : Ω] → {α : Type} → Typed.Datatype.Ctor α → Datatype.Ctor -/
#guard_msgs in #check @Cvc.Typed.Datatype.Ctor.toUntyped

/-- info: @Typed.Datatype.Field.erase : {α β : Type} → [inst : Ω] → Typed.Datatype.Field α β → Datatype.Selector -/
#guard_msgs in #check @Cvc.Typed.Datatype.Field.erase

/-- info: @Typed.Datatype.Field.toUntyped : {α β : Type} → [inst : Ω] → Typed.Datatype.Field α β → Datatype.Selector -/
#guard_msgs in #check @Cvc.Typed.Datatype.Field.toUntyped

/-- info: @Typed.Fields.erase : {fields : List (String × Type)} →
  [inst : Ω] → Typed.Fields fields → Untyped.Fields (List.map Prod.fst fields) -/
#guard_msgs in #check @Cvc.Typed.Fields.erase

/-- info: @Typed.Fields.toUntyped : {fields : List (String × Type)} →
  [inst : Ω] → Typed.Fields fields → Untyped.Fields (List.map Prod.fst fields) -/
#guard_msgs in #check @Cvc.Typed.Fields.toUntyped

/-- info: @Typed.Grammar.erase : {σ : Type} → [inst : Ω] → Typed.Grammar σ → Untyped.Grammar -/
#guard_msgs in #check @Cvc.Typed.Grammar.erase

/-- info: @Typed.Grammar.toUntyped : {σ : Type} → [inst : Ω] → Typed.Grammar σ → Untyped.Grammar -/
#guard_msgs in #check @Cvc.Typed.Grammar.toUntyped

/-- info: @Typed.NT.erase : [inst : Ω] → {α : Type} → Typed.NT α → Untyped.NT -/
#guard_msgs in #check @Cvc.Typed.NT.erase

/-- info: @Typed.NT.toUntyped : [inst : Ω] → {α : Type} → Typed.NT α → Untyped.NT -/
#guard_msgs in #check @Cvc.Typed.NT.toUntyped

/-- info: @Typed.NTs.erase : [inst : Ω] → Typed.NTs → Untyped.NTs -/
#guard_msgs in #check @Cvc.Typed.NTs.erase

/-- info: @Typed.NTs.toUntyped : [inst : Ω] → Typed.NTs → Untyped.NTs -/
#guard_msgs in #check @Cvc.Typed.NTs.toUntyped

/-- info: @Typed.Solver.Heap.erase : [inst : Ω] →
  {α β : Type} → {solver : Typed.Solver} → solver.Heap α β → Untyped.Solver.Heap solver -/
#guard_msgs in #check @Cvc.Typed.Solver.Heap.erase

/-- info: @Typed.Solver.Heap.toUntyped : [inst : Ω] →
  {α β : Type} → {solver : Typed.Solver} → solver.Heap α β → Untyped.Solver.Heap solver -/
#guard_msgs in #check @Cvc.Typed.Solver.Heap.toUntyped

/-- info: @Typed.Solver.Proof.relax : {pc : Proof.Component} →
  [inst : Ω] → {s : Typed.Solver} → s.Proof pc → Untyped.Solver.Proof s pc -/
#guard_msgs in #check @Cvc.Typed.Solver.Proof.relax

/-- info: @Typed.Solver.Proof.toUntyped : {pc : Proof.Component} →
  [inst : Ω] → {s : Typed.Solver} → s.Proof pc → Untyped.Solver.Proof s pc -/
#guard_msgs in #check @Cvc.Typed.Solver.Proof.toUntyped

/-- info: @Typed.Solver.relax : [inst : Ω] → Typed.Solver → Untyped.Solver -/
#guard_msgs in #check @Cvc.Typed.Solver.relax

/-- info: @Typed.Solver.toUntyped : [inst : Ω] → Typed.Solver → Untyped.Solver -/
#guard_msgs in #check @Cvc.Typed.Solver.toUntyped

/-- info: @Typed.Term.Args.erase : [inst : Ω] → {φ β : Type} → Typed.Term.Args φ β → Untyped.Terms -/
#guard_msgs in #check @Cvc.Typed.Term.Args.erase

/-- info: @Typed.Term.Args.toUntyped : [inst : Ω] → {φ β : Type} → Typed.Term.Args φ β → Untyped.Terms -/
#guard_msgs in #check @Cvc.Typed.Term.Args.toUntyped

/-- info: @Typed.Term.Components.erase : [inst : Ω] → {α : Type} → Typed.Term.Components α → Untyped.Terms -/
#guard_msgs in #check @Cvc.Typed.Term.Components.erase

/-- info: @Typed.Term.Components.toUntyped : [inst : Ω] → {α : Type} → Typed.Term.Components α → Untyped.Terms -/
#guard_msgs in #check @Cvc.Typed.Term.Components.toUntyped

/-- info: @Typed.Term.Tup.Components.erase : [inst : Ω] →
  {α : List Type} → {β : Type} → Typed.Term.Tup.Components α β → Untyped.Terms -/
#guard_msgs in #check @Cvc.Typed.Term.Tup.Components.erase

/-- info: @Typed.Term.Tup.Components.toUntyped : [inst : Ω] →
  {α : List Type} → {β : Type} → Typed.Term.Tup.Components α β → Untyped.Terms -/
#guard_msgs in #check @Cvc.Typed.Term.Tup.Components.toUntyped

/-- info: @Typed.Term.erase : [inst : Ω] → {α : Type} → Typed.Term α → Untyped.Term -/
#guard_msgs in #check @Cvc.Typed.Term.erase

/-- info: @Typed.Term.toUntyped : [inst : Ω] → {α : Type} → Typed.Term α → Untyped.Term -/
#guard_msgs in #check @Cvc.Typed.Term.toUntyped

/-- info: @Typed.TermToValue.toUntyped : {α : Type} → [A : Typed.TermToValue α] → Untyped.TermToValue α -/
#guard_msgs in #check @Cvc.Typed.TermToValue.toUntyped

/-- info: @Typed.ValueToTerm.toUntyped : {α : Type} → [A : Typed.ValueToTerm α] → Untyped.ValueToTerm α -/
#guard_msgs in #check @Cvc.Typed.ValueToTerm.toUntyped

/-- info: @Untyped.BVar.toTyped : [inst : Ω] → {α : Type} → [ToTyp α] → Untyped.BVar → Env (Typed.BVar α) -/
#guard_msgs in #check @Cvc.Untyped.BVar.toTyped

/-- info: @Untyped.BVar.toTypedAs : [inst : Ω] → (α : Type) → [ToTyp α] → Untyped.BVar → Env (Typed.BVar α) -/
#guard_msgs in #check @Cvc.Untyped.BVar.toTypedAs

/-- info: @Untyped.BVar.typeCheck : [inst : Ω] → {α : Type} → [ToTyp α] → Untyped.BVar → Env (Typed.BVar α) -/
#guard_msgs in #check @Cvc.Untyped.BVar.typeCheck

/-- info: @Untyped.BVar.typeCheckAs : [inst : Ω] → (α : Type) → [ToTyp α] → Untyped.BVar → Env (Typed.BVar α) -/
#guard_msgs in #check @Cvc.Untyped.BVar.typeCheckAs

/-- info: @Untyped.Fields.toTyped : [inst : Ω] →
  {fields : List (String × Type)} →
    {names : List String} →
      [ToTypFields fields] →
        Untyped.Fields names →
          autoParam (names = List.map Prod.fst fields) Untyped.Fields.toTyped._auto_1 → Env (Typed.Fields fields) -/
#guard_msgs in #check @Cvc.Untyped.Fields.toTyped

/-- info: @Untyped.Fields.toTypedAs : [inst : Ω] →
  {names : List String} →
    (fields : List (String × Type)) →
      [Fs : ToTypFields fields] →
        Untyped.Fields names →
          autoParam (names = List.map Prod.fst fields) Untyped.Fields.toTypedAs._auto_1 → Env (Typed.Fields fields) -/
#guard_msgs in #check @Cvc.Untyped.Fields.toTypedAs

/-- info: @Untyped.Fields.typeCheck : [inst : Ω] →
  {fields : List (String × Type)} →
    {names : List String} →
      [ToTypFields fields] →
        Untyped.Fields names →
          autoParam (names = List.map Prod.fst fields) Untyped.Fields.toTyped._auto_1 → Env (Typed.Fields fields) -/
#guard_msgs in #check @Cvc.Untyped.Fields.typeCheck

/-- info: @Untyped.Fields.typeCheckAs : [inst : Ω] →
  {names : List String} →
    (fields : List (String × Type)) →
      [Fs : ToTypFields fields] →
        Untyped.Fields names →
          autoParam (names = List.map Prod.fst fields) Untyped.Fields.toTypedAs._auto_1 → Env (Typed.Fields fields) -/
#guard_msgs in #check @Cvc.Untyped.Fields.typeCheckAs

/-- info: @Untyped.Grammar.toTyped : [inst : Ω] → {σ : Type} → [ToTyp σ] → Untyped.Grammar → Env (Typed.Grammar σ) -/
#guard_msgs in #check @Cvc.Untyped.Grammar.toTyped

/-- info: @Untyped.Grammar.toTypedAs : [inst : Ω] → (σ : Type) → [ToTyp σ] → Untyped.Grammar → Env (Typed.Grammar σ) -/
#guard_msgs in #check @Cvc.Untyped.Grammar.toTypedAs

/-- info: @Untyped.Grammar.typeCheck : [inst : Ω] → {σ : Type} → [ToTyp σ] → Untyped.Grammar → Env (Typed.Grammar σ) -/
#guard_msgs in #check @Cvc.Untyped.Grammar.typeCheck

/-- info: @Untyped.Grammar.typeCheckAs : [inst : Ω] → (σ : Type) → [ToTyp σ] → Untyped.Grammar → Env (Typed.Grammar σ) -/
#guard_msgs in #check @Cvc.Untyped.Grammar.typeCheckAs

/-- info: @Untyped.NT.toTyped : [inst : Ω] → {α : Type} → [ToTyp α] → Untyped.NT → Env (Typed.NT α) -/
#guard_msgs in #check @Cvc.Untyped.NT.toTyped

/-- info: @Untyped.NT.toTypedAs : [inst : Ω] → (α : Type) → [ToTyp α] → Untyped.NT → Env (Typed.NT α) -/
#guard_msgs in #check @Cvc.Untyped.NT.toTypedAs

/-- info: @Untyped.NT.typeCheck : [inst : Ω] → {α : Type} → [ToTyp α] → Untyped.NT → Env (Typed.NT α) -/
#guard_msgs in #check @Cvc.Untyped.NT.typeCheck

/-- info: @Untyped.NT.typeCheckAs : [inst : Ω] → (α : Type) → [ToTyp α] → Untyped.NT → Env (Typed.NT α) -/
#guard_msgs in #check @Cvc.Untyped.NT.typeCheckAs

/-- info: @Untyped.Solver.Heap.toTyped : [inst : Ω] →
  {α β : Type} → [ToTyp α] → [ToTyp β] → {solver : Typed.Solver} → Untyped.Solver.Heap solver → Env (solver.Heap α β) -/
#guard_msgs in #check @Cvc.Untyped.Solver.Heap.toTyped

/-- info: @Untyped.Solver.Heap.toTypedAs : [inst : Ω] →
  (α β : Type) → [ToTyp α] → [ToTyp β] → {solver : Typed.Solver} → Untyped.Solver.Heap solver → Env (solver.Heap α β) -/
#guard_msgs in #check @Cvc.Untyped.Solver.Heap.toTypedAs

/-- info: @Untyped.Solver.Heap.typeCheck : [inst : Ω] →
  {α β : Type} → [ToTyp α] → [ToTyp β] → {solver : Typed.Solver} → Untyped.Solver.Heap solver → Env (solver.Heap α β) -/
#guard_msgs in #check @Cvc.Untyped.Solver.Heap.typeCheck

/-- info: @Untyped.Solver.Heap.typeCheckAs : [inst : Ω] →
  (α β : Type) → [ToTyp α] → [ToTyp β] → {solver : Typed.Solver} → Untyped.Solver.Heap solver → Env (solver.Heap α β) -/
#guard_msgs in #check @Cvc.Untyped.Solver.Heap.typeCheckAs

/-- info: @Untyped.Solver.Proof.toTyped : {pc : Proof.Component} →
  [inst : Ω] → {s : Untyped.Solver} → s.Proof pc → Typed.Solver.Proof s pc -/
#guard_msgs in #check @Cvc.Untyped.Solver.Proof.toTyped

/-- info: @Untyped.Solver.toTyped : [inst : Ω] → Untyped.Solver → Typed.Solver -/
#guard_msgs in #check @Cvc.Untyped.Solver.toTyped

/-- info: @Untyped.Term.toTyped : [inst : Ω] → {α : Type} → [ToTyp α] → Untyped.Term → Env (Typed.Term α) -/
#guard_msgs in #check @Cvc.Untyped.Term.toTyped

/-- info: @Untyped.Term.toTypedAs : [inst : Ω] → (α : Type) → [ToTyp α] → Untyped.Term → Env (Typed.Term α) -/
#guard_msgs in #check @Cvc.Untyped.Term.toTypedAs

/-- info: @Untyped.Term.typeCheck : [inst : Ω] → {α : Type} → [ToTyp α] → Untyped.Term → Env (Typed.Term α) -/
#guard_msgs in #check @Cvc.Untyped.Term.typeCheck

/-- info: @Untyped.Term.typeCheckAs : [inst : Ω] → (α : Type) → [ToTyp α] → Untyped.Term → Env (Typed.Term α) -/
#guard_msgs in #check @Cvc.Untyped.Term.typeCheckAs

/-- info: @Untyped.TermToValue.toTyped : {α : Type} → [A : Untyped.TermToValue α] → Typed.TermToValue α -/
#guard_msgs in #check @Cvc.Untyped.TermToValue.toTyped

/-- info: @Untyped.ValueToTerm.toTyped : {α : Type} → [ToTyp α] → [A : Untyped.ValueToTerm α] → Typed.ValueToTerm α -/
#guard_msgs in #check @Cvc.Untyped.ValueToTerm.toTyped



/-! ## The conversions at work

The ones not exercised beside their types: the spines going down, the solver and its proofs both
ways, and the value classes. -/

/-- info:
tuple    : #[1, true]
tup      : #[1, true]
args     : #[1, true]
solver   : true
-/
#guard_msgs in #eval Env.runIO do
  let one ← Typed.Term.mkInt 1
  let tru ← Typed.Term.mkTrue
  println! "tuple    : {(Typed.Term.Components.cons one (.last tru)).toUntyped}"
  println! "tup      : {(Typed.Term.Tup.Components.cons one (.last tru)).erase}"
  let args : Typed.Term.Args (Int → Bool → Int) Int := .cons one (.last tru)
  println! "args     : {args.erase}"
  let s ← Typed.Solver.new
  let s' : Typed.Solver := s.relax.toTyped
  println! "solver   : {(← s'.getOption "produce-models") == (← s.getOption "produce-models")}"

/-- A proof goes down and back up for free, both layers sharing the proof type. -/
example [Ω] (s : Typed.Solver) (p : s.Proof .full) : s.Proof .full := p.relax.toTyped

/-! A type with sort-erased conversions alone is usable typed: the bridge from sort-erased checks
the term it builds against the index, and erases the term it reads. -/

/-- A Lean type denoting `Int`, given only sort-erased conversions. -/
structure Celsius where
  deg : Int

instance : ToTyp Celsius := ⟨.int⟩

instance : Untyped.ValueToTerm Celsius := ⟨fun c => Untyped.Term.mkInt c.deg⟩

instance : Untyped.TermToValue Celsius := ⟨fun t => return ⟨← t.getIntValue⟩⟩

/-- info:
built : 21
read  : 21
-/
#guard_msgs in #eval Env.runIO do
  let s ← Typed.Solver.new
  s.setOption "produce-models" "true"
  let t ← Typed.Term.mkValue (⟨21⟩ : Celsius)
  println! "built : {t}"
  let x ← s.declareConstAs Celsius "x"
  s.assert (← Typed.Term.equal x t)
  let c ← s.checkSat (ifSat := s.getValue x)
  println! "read  : {c.deg}"
