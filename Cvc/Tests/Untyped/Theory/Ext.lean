/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Core
import Cvc.Untyped.Theory
import Cvc.Untyped.Core.Bool
import Cvc.Types.Set
-- the `match` notation expands to `Cvc.Untyped.Term.…` names that live here, and a macro's
-- names resolve at the use site
import Cvc.Untyped.Theory.Datatype

public meta import Cvc.Untyped.Theory.Datatype
public meta import Cvc.Untyped.Core
public meta import Cvc.Untyped.Theory
public meta import Cvc.Untyped.Core.Bool
public meta import Cvc.Types.Set



/-! # The `smt!` DSL, sort-erased

What is tested here is what `Cvc/Ext.lean` itself declares: the forms that mention no theory. A
theory's own notation — `∧`, `+`, `∪`, `match`, `{a := t}` — is declared beside that theory's
constructors and tested beside them too, so this file does not depend on theories a reader of it
has no reason to care about. `open Cvc.Untyped` selects this layer's `smt!`, which expands to
fully-qualified `Cvc.Untyped.Term.…` calls, so nothing else has to be in scope.
-/
namespace Cvc.Tests.Untyped.Term.Ext

open Cvc
open Cvc.Untyped


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
nested   : (+ (+ i j) i)
-/
#guard_msgs in #eval Env.runIO do
  let i ← Cvc.Untyped.Term.mkSymbolAs Int "i"
  let j ← Cvc.Untyped.Term.mkSymbolAs Int "j"

  println! "ident    : {← smt! i}"
  println! "escape   : {← smt! ![Cvc.Untyped.Term.add i j]}"
  println! "paren    : {← smt! (i + j) * i}"
  println! "let      : {← smt! let x ← i + j; x < i}"
  println! "nested   : {← smt! ![smt! i + j] + i}"

/-! ## Application

`f i b` is spelled as Lean spells it, and expands to `applyN`, so it **flattens**: the nested
spelling `(f i) b` builds the very same term rather than a function-sorted intermediate. Arguments
parse at `max`, so an operator, `if`, `let` or `match` in argument position needs parentheses —
again exactly as in Lean.
-/

/-- info:
apply      : (f i b)
partial    : (f i)
nested     : (f i b)
flattens   : true
arg expr   : (f (+ i 1) b)
in expr    : (+ (f i b) 1)
under ¬    : (not (= (f i b) 1))
higher-ord : (hof f)
-/
#guard_msgs in #eval Env.runIO do
  let f ← Cvc.Untyped.Term.mkSymbolAs (Int → Bool → Int) "f"
  let hof ← Cvc.Untyped.Term.mkSymbolAs ((Int → Bool → Int) → Int) "hof"
  let i ← Cvc.Untyped.Term.mkSymbolAs Int "i"
  let b ← Cvc.Untyped.Term.mkSymbolAs Bool "b"

  let flat ← smt! f i b
  let nested ← smt! (f i) b
  println! "apply      : {flat}"
  println! "partial    : {← smt! f i}"
  println! "nested     : {nested}"
  println! "flattens   : {flat == nested}"
  println! "arg expr   : {← smt! f (i + 1) b}"
  println! "in expr    : {← smt! (f i b) + 1}"
  println! "under ¬    : {← smt! ¬ (f i b) = 1}"
  println! "higher-ord : {← smt! hof f}"

