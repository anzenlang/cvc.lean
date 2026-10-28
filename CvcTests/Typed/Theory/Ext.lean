/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Core
import Cvc.Typed.Theory
import Cvc.Typed.Core.Bool
import Cvc.Types.Set
-- the `match` notation expands to `Cvc.Typed.…` names that live here, and a macro's names
-- resolve at the use site
import Cvc.Typed.Theory.Datatype

public meta import Cvc.Typed.Theory.Datatype
public meta import Cvc.Typed.Core
public meta import Cvc.Typed.Theory
public meta import Cvc.Typed.Core.Bool
public meta import Cvc.Types.Set



/-! # The `smt!` DSL, typed

What is tested here is what `Cvc/Ext.lean` itself declares: the forms that mention no theory. A
theory's own notation — `∧`, `+`, `∪`, `match`, `{a := t}` — is declared beside that theory's
constructors and tested beside them too, along with the index each expansion produces, so this file
does not depend on theories a reader of it has no reason to care about.

`open Cvc.Typed` selects a `smt!` that expands to fully-qualified `Cvc.Typed.Term.…` calls, so the
resulting terms carry their Lean index.
-/
namespace Cvc.Tests.Typed.Term.Ext

open Cvc
open Cvc.Typed


/-! ## The theory-free forms

Only these live in `Cvc/Ext.lean`: a parenthesis, the `![…]` escape into Lean, an identifier,
application, and `let`. Every other form belongs to a theory and is tested with it — without that
theory's import the form does not parse at all, which is the point of the split.
-/

/-- info:
ident    : i
escape   : (+ i j)
paren    : (* (+ i j) i)
let      : (< (+ i j) i)
-/
#guard_msgs in #eval Env.runIO do
  let i ← Cvc.Typed.Term.mkSymbolAs Int "i"
  let j ← Cvc.Typed.Term.mkSymbolAs Int "j"

  println! "ident    : {← smt! i}"
  println! "escape   : {← smt! ![Cvc.Typed.Term.add i j]}"
  println! "paren    : {← smt! (i + j) * i}"
  println! "let      : {← smt! let x ← i + j; x < i}"

section indices
variable [Ω] (i j : Term Int) (f : Term (Int → Bool → Int)) (b : Term Bool)

/-- A `let` binding is indexed too. -/
example : Env (Term Bool) := smt! let x ← i + j; x < i
/-- A saturating application lands at the function's codomain. -/
example : Env (Term Int) := smt! f i b
/-- A partial one keeps the arrows its arguments did not consume. -/
example : Env (Term (Bool → Int)) := smt! f i
/-- An application is an operand like any other. -/
example : Env (Term Bool) := smt! (f i b) < j

end indices

/-! ## Application

`f i b` is spelled as Lean spells it, and expands to `applyN` over an `Args` spine, so the index
follows the arrows the arguments consume: saturating gives the codomain, stopping early gives the
*remaining* function index. It flattens, inheriting that from the sort-erased constructor.
-/

/-- info:
apply      : (f i b)
partial    : (f i)
nested     : (f i b)
flattens   : true
arg expr   : (f (+ i 1) b)
in expr    : (+ (f i b) 1)
higher-ord : (hof f)
-/
#guard_msgs in #eval Env.runIO do
  let f ← Cvc.Typed.Term.mkSymbolAs (Int → Bool → Int) "f"
  let hof ← Cvc.Typed.Term.mkSymbolAs ((Int → Bool → Int) → Int) "hof"
  let i ← Cvc.Typed.Term.mkSymbolAs Int "i"
  let b ← Cvc.Typed.Term.mkSymbolAs Bool "b"

  let flat : Term Int ← smt! f i b
  let nested : Term Int ← smt! (f i) b
  println! "apply      : {flat}"
  println! "partial    : {← (smt! f i : Env (Term (Bool → Int)))}"
  println! "nested     : {nested}"
  println! "flattens   : {flat == nested}"
  println! "arg expr   : {← (smt! f (i + 1) b : Env (Term Int))}"
  println! "in expr    : {← (smt! (f i b) + 1 : Env (Term Int))}"
  println! "higher-ord : {← (smt! hof f : Env (Term Int))}"
