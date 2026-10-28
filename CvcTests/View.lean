/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Untyped.View
public import Cvc.Typed.View

public meta import Cvc.Untyped.View
public meta import Cvc.Typed.View



/-! # The `View` modules alone

`Cvc.Untyped.View` and `Cvc.Typed.View` are all it takes to inspect and rewrite terms: the
aggregate's leaves — values, symbols, bound variables — need no theory, so with no theory imported
`def.term_view` gathers only the Boolean view, and the traversals come along.
-/
namespace Cvc.Tests.View

open Cvc

namespace Erased

open Cvc.Untyped

public section variable [Ω]

def.term_view V

end

/-- info: @V.bvar : [inst : Ω] → BVar → V -/
#guard_msgs in #check @V.bvar

/-- info: 4 -/
#guard_msgs in #eval Env.runIO do
  let p ← Term.mkSymbol (← Srt.bool) "p"
  let t ← Term.and p (← Term.not p)
  println! ← t.fold 0 (pre := fun _ (_ : V) n => return .descend (n + 1))

end Erased

namespace Indexed

open Cvc.Typed

public section variable [Ω]

def.term_view V

end

/-- info: @V.bvar : [inst : Ω] → {τ : Typ} → BVar τ.Denote → V τ -/
#guard_msgs in #check @V.bvar

/-- info: @V.and : [inst : Ω] → Kids Bool → V Typ.bool -/
#guard_msgs in #check @V.and

/-- info: (and p p) -/
#guard_msgs in #eval Env.runIO do
  let p ← Term.mkSymbolAs Bool "p"
  let t ← Term.and p (← Term.not (← Term.not p))
  let (s, _) ← t.walk () (pre := fun {τ} _ (v : V τ) _ => match τ, v with
    | .bool, .not t => do
      match ← V.of .bool t with
      | .not u => return .replace u ()
      | _ => return .descend ()
    | _, _ => return .descend ())
  println! s

end Indexed
