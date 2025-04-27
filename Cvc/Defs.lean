/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Init
import Cvc.Srt.Types



namespace Cvc



/-- A type-safe cvc term.

This is just a strongly-typed wrapper around an *unsafe term* (`cvc5.Term`). Values of this type can
only be created in this module. The constructor is therefore private.
-/
structure Term (α : Type) extends AsSrt α where
/-- Private constructor.. -/
private ofUnsafe' ::
  /-- Unsafe term accessor. -/
  toUnsafe : cvc5.Term



namespace Term

open cvc5 renaming TermManager → Tm



/-- Cvc term builder transformer monad. -/
abbrev BuildT (m : Type → Type) :=
  ExceptT Error (StateT Tm m)

/-- Cvc term builder monad. -/
abbrev Build := BuildT Id



/-- Private constructor with implicit `ToSrt α` instance. -/
private
def ofUnsafe [AsSrt α] (term : cvc5.Term) : Term α :=
  Term.ofUnsafe' inferInstance term

/-- Monadic private constructor. -/
private
def ofUnsafeM [Monad m] [AsSrt α] (term : m cvc5.Term) : m (Term α) :=
  Term.ofUnsafe <$> term



section variable (term : Term α)

instance instToSrt : ToSrt α := term.toToSrt


/-- Reframes the type parameter of a term as its `srt : Srt`. -/
abbrev asSrt : Term term.srt :=
  term.eq_srt ▸ term

/-- Facilitates pattern-matching on the sort (`Srt`) of a term. -/
def srtInspect (f : (srt : Srt) → Term srt → γ) : γ :=
  f term.srt term.asSrt

/-- SMT-LIB string representation. -/
protected
def toString (t : Term α) : String :=
  t.toUnsafe.toString

instance : ToString (Term α) := ⟨Term.toString⟩

end
