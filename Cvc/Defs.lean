/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Init
import Cvc.Srt



namespace Cvc

/-- Strongly-typed term.

This is just a wrapper around an unsafe term (`cvc5.Term`).

- Constructor is private for type-safety reasons.
- Accessor is public as this does not impact type-safety.
-/
inductive Term {γ : Type u} : γ → Type u
/-- **[private]** Constructor from an unsafe term.

Private as this would allow user creating term of any `Srt`/`Type`
-/
| private ofUnsafe {a : γ} (toUnsafe : cvc5.Term) : Term a

abbrev Term0 := Term (γ := Srt)

abbrev Term1 := Term (γ := Type)

-- with this version of `Term` we can pass `Srt` values and types
namespace Test

/-- info: Term Srt.bool : Type -/
#guard_msgs in #check Term Srt.bool
/-- info: Term0 Srt.bool : Type -/
#guard_msgs in #check Term0 Srt.bool

/-- info: Term Bool : Type 1 -/
#guard_msgs in #check Term Bool
/-- info: Term1 Bool : Type 1 -/
#guard_msgs in #check Term1 Bool

end Test



namespace Term

/-- **[private]** Monadic term constructor. -/
def ofUnsafeM [Monad m] : m cvc5.Term → m (Term α) :=
  (Term.ofUnsafe <$> ·)

protected
def srt {srt : Srt} : Term srt → Srt :=
  fun _ => srt

/-- Unsafe term accessor. -/
def toUnsafe : Term α → cvc5.Term
| Term.ofUnsafe term => term

/-- Turns a `Term0` into a `Term1`. -/
def liftWith (Driver : Type) [I : Srt.ToType Driver] : Term srt → Term (I.srtToType srt)
| Term.ofUnsafe term => Term.ofUnsafe term

@[inherit_doc liftWith]
def lift {Driver} [I : Srt.ToType Driver] (term : Term srt) : Term (I.srtToType srt) :=
  liftWith Driver term

/-- Turns a `Term1` into a `Term0`. -/
def asSrt [ToSrt α] : Term α → Term (Srt.ofType α)
| Term.ofUnsafe term => Term.ofUnsafe term

/-- Facilitates pattern-matching on the `Srt` of a `Term1`. -/
def inspectSrt [ToSrt α] (t : Term α) (f : (srt : Srt) → Term srt → γ) : γ :=
  let t := t.asSrt
  f t.srt t

/-- SMT-LIB string representation. -/
protected
def toSmtString : Term α → String
| Term.ofUnsafe t => t.toString

instance : ToString (Term α) := ⟨Term.toSmtString⟩



section abbrevs

protected
abbrev bool := Term0 .bool

protected
abbrev int := Term0 .int

protected
abbrev abstract (kind : Srt.Kind) := Term0 (.abstract kind)

protected
abbrev array (idx elm : Srt) := Term0 (.array idx elm)

end abbrevs


open cvc5 renaming TermManager → Tm



/-- Cvc term builder transformer monad. -/
abbrev Build :=
  ExceptT Error (StateM Tm)

instance : MonadLift (Except cvc5.Error) Build where
  monadLift code tm := do
    match ← code with
    | .ok res => return (.ok res, tm)
    | .error e => return (.error <| Error.ofCvc5 e, tm)

/-- Type-unsafe term constructor. -/
private
def mkTerm (k : cvc5.Kind) (args : Array cvc5.Term) : Build (Term0 srt) := do
  let tm ← get
  let uTerm ← tm.mkTerm k args
  return Term.ofUnsafe uTerm

private
def tmDoM [Monad m] [MonadLiftT m Build] (f : Tm → m γ) : Build γ :=
  get >>= (liftM <| f ·)

private
def tmDo (f : Tm → γ) : Build γ := tmDoM (m := Id) f

namespace mk

/-- Boolean constant constructor. -/
protected
def bool (b : Bool) : Build Term.bool :=
  tmDo (· |>.mkBoolean b |> Term.ofUnsafe)

/-- Integer constant constructor.-/
protected
def int (i : Int) : Build Term.bool :=
  tmDo (· |>.mkInteger i |> Term.ofUnsafe)

/-- If-then-else constructor. -/
def mkIte (cnd : Term.bool) (thn els : Term0 α) : Build (Term0 α) :=
  mkTerm .ITE #[cnd.toUnsafe, thn.toUnsafe, els.toUnsafe]
