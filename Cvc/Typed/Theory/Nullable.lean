/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Typed.Theory.Nullable.Defs
public import Cvc.Typed.Theory.Nullable.Arith
public import Cvc.Typed.Theory.Nullable.Array
public import Cvc.Typed.Theory.Nullable.Bag
public import Cvc.Typed.Theory.Nullable.BitVec
public import Cvc.Typed.Theory.Nullable.Bool
public import Cvc.Typed.Theory.Nullable.FiniteField
public import Cvc.Typed.Theory.Nullable.Float
public import Cvc.Typed.Theory.Nullable.Regex
public import Cvc.Typed.Theory.Nullable.Seq
public import Cvc.Typed.Theory.Nullable.Set
public import Cvc.Typed.Theory.Nullable.String



/-! # Nullables, typed

cvc5's `Nullable` sort is Lean's `Option`: `Term.mkNull`, `Term.nullableSome` and the rest build and
read `Term (Option α)`, and each theory's operators have a lifted form named with a `?`, such as
`Term.add? : Term (Option α) → Term (Option α) → Env (Term (Option α))`. A lifted operator is
strict: its result is null as soon as one argument is.
-/
