/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Safe.Smt



namespace Cvc.Safe



declare_syntax_cat smterm


syntax "[" term "]" : smterm
syntax "![" term "]" : smterm

syntax "(" smterm ")" : smterm

syntax ident : smterm
syntax name : smterm
syntax num : smterm

syntax smterm " → " smterm : smterm
syntax smterm " ∧ " smterm : smterm
syntax smterm " ∨ " smterm : smterm
syntax "¬ " smterm : smterm

syntax "if " smterm " then " smterm " else " smterm : smterm
syntax "let " ident " ← " smterm ppLine smterm : smterm

syntax smterm " = " smterm : smterm
syntax smterm " ≠ " smterm : smterm
syntax smterm " ≤ " smterm : smterm
syntax smterm " ≥ " smterm : smterm
syntax smterm " < " smterm : smterm
syntax smterm " > " smterm : smterm

syntax smterm " * " smterm : smterm
syntax smterm " / " smterm : smterm
syntax smterm " + " smterm : smterm
syntax smterm " - " smterm : smterm
syntax "- " smterm : smterm

syntax "smt! " smterm : term
syntax "smt! " ident+ " => " smterm : term

macro_rules
| `(smt! $[ $i ]* => $t:smterm ) => `(
  fun $[ $i ]* => smt! $t
)

| `(smt! [ $t:term ]) => `((pure $t))
| `(smt! ![ $t:term ]) => `($t)
| `(smt! ($t:smterm)) => `(smt! $t)

| `(smt! $n:ident) => `(pure $n)
| `(smt! $n:name) => `(pure $n)
| `(smt! $n:num) => `(Cvc.Safe.Term.mkInt $n)
| `(smt! - $n:num) => `(Cvc.Safe.Term.mkInt (- $n))

| `(smt! $lft → $rgt) =>
  `( (do (← smt! $lft).implies (← smt! $rgt)) )
| `(smt! $lft ∧ $rgt) =>
  `( (do (← smt! $lft).and (← smt! $rgt)) )
| `(smt! $lft ∨ $rgt) =>
  `( (do (← smt! $lft).or (← smt! $rgt)) )
| `(smt! ¬ $t) =>
  `( (do (← smt! $t).not) )

| `(smt! if $cnd then $thn else $els) =>
  `( (do (← smt! $cnd).ite (← smt! $thn) (← smt! $els)) )

| `(smt! let $id ← $idDef $tail) =>
  `( (do
        let $id ← smt! $idDef
        smt! $tail
  ) )

| `(smt! $lft = $rgt) =>
  `( (do (← smt! $lft).eq (← smt! $rgt)) )
| `(smt! $lft ≠ $rgt) =>
  `( (do Cvc.Safe.Term.mkDistinct #[(← smt! $lft), (← smt! $rgt)]) )
| `(smt! $lft ≤ $rgt) =>
  `( (do (← smt! $lft).le (← smt! $rgt)) )
| `(smt! $lft ≥ $rgt) =>
  `( (do (← smt! $lft).ge (← smt! $rgt)) )
| `(smt! $lft < $rgt) =>
  `( (do (← smt! $lft).lt (← smt! $rgt)) )
| `(smt! $lft > $rgt) =>
  `( (do (← smt! $lft).gt (← smt! $rgt)) )

| `(smt! $lft * $rgt) =>
  `( (do (← smt! $lft).mult (← smt! $rgt)) )
-- | `(smt! $lft / $rgt) =>
--   `( (do (← smt! $lft).ge (← smt! $rgt)) )
| `(smt! $lft + $rgt) =>
  `( (do (← smt! $lft).add (← smt! $rgt)) )
| `(smt! - $t) =>
  `( (do (← smt! $t).neg) )
| `(smt! $lft - $rgt) =>
  `( (do (← smt! $lft).sub (← smt! $rgt)) )
