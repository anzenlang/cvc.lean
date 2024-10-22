/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Safe.Smt



namespace Cvc.Safe



declare_syntax_cat smterm


-- syntax "[|" term "|]" : smterm
-- syntax "![" term "]" : smterm

syntax "(" smterm ")" : smterm

syntax ident : smterm
syntax name : smterm
syntax num : smterm

syntax:25 smterm:26 " → " smterm:25 : smterm
syntax:35 smterm:36 " ∧ " smterm:35 : smterm
syntax:30 smterm:31 " ∨ " smterm:30 : smterm
syntax:max "¬ " smterm:40 : smterm

syntax
  withPosition("if " (colGt smterm) " then " (colGt smterm) " else " (colGt smterm))
: smterm
syntax "let " ident " ← " smterm "; " ppLine smterm : smterm

syntax:50 smterm:51 " = " smterm:50 : smterm
syntax:50 smterm:51 " ≠ " smterm:50 : smterm
syntax:50 smterm:51 " ≤ " smterm:50 : smterm
syntax:50 smterm:51 " ≥ " smterm:50 : smterm
syntax:50 smterm:51 " < " smterm:50 : smterm
syntax:50 smterm:51 " > " smterm:50 : smterm

syntax:70 smterm:70 " * " smterm:71 : smterm
syntax:70 smterm:70 " /! " smterm:71 : smterm
syntax:70 smterm:70 " /. " smterm:71 : smterm
syntax:70 smterm:70 " /.! " smterm:71 : smterm
syntax:70 smterm:70 " / " smterm:71 : smterm
syntax:70 smterm:70 " % " smterm:71 : smterm
syntax:65 smterm:65 " + " smterm:66 : smterm
syntax:65 smterm:65 " - " smterm:66 : smterm
syntax:75 "- " smterm : smterm

syntax:100 smterm:100 (colGt smterm:101) : smterm

syntax "smt! " ppLine (colGt smterm) : term
open Lean.Parser.Term in
syntax "smt! " "fun" (ppSpace funBinder)+ optType " => " ppLine (colGt smterm) : term
#eval 1 + 3
macro_rules
| `(smt! fun $binders $optTy => $t:smterm ) => `(
  fun $binders $optTy => smt! $t
)
| `(smt! fun $binders => $t:smterm ) => `(
  fun $binders => smt! $t
)

-- | `(smt! [| $t:term |]) => `((pure $t))
-- | `(smt! ![ $t:term ]) => `($t)
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

| `(smt! let $id ← $idDef ; $tail) =>
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

| `(smt! $f:smterm $arg:smterm) =>
  `( (do
    (← smt! $f).apply (← smt! $arg)
  ) )

| `(smt! $lft * $rgt) =>
  `( (do (← smt! $lft).mult (← smt! $rgt)) )
| `(smt! $lft / $rgt) =>
  `( (do (← smt! $lft).intDivTotal (← smt! $rgt)) )
| `(smt! $lft /! $rgt) =>
  `( (do (← smt! $lft).intDiv (← smt! $rgt)) )
| `(smt! $lft /. $rgt) =>
  `( (do (← smt! $lft).ratDiv (← smt! $rgt)) )
| `(smt! $lft /.! $rgt) =>
  `( (do (← smt! $lft).ratDivTotal (← smt! $rgt)) )
| `(smt! $lft + $rgt) =>
  `( (do (← smt! $lft).add (← smt! $rgt)) )
| `(smt! - $t) =>
  `( (do (← smt! $t).neg) )
| `(smt! $lft - $rgt) =>
  `( (do (← smt! $lft).sub (← smt! $rgt)) )
