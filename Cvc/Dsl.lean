/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Defs



namespace Cvc.Term.Dsl

declare_syntax_cat smtTerm


-- scoped syntax "[|" term "|]" : smtTerm
scoped syntax "![" term "]" : smtTerm

scoped syntax "(" smtTerm ")" : smtTerm

scoped syntax ident : smtTerm
scoped syntax name : smtTerm
scoped syntax num : smtTerm

scoped syntax:25 smtTerm:26 " → " smtTerm:25 : smtTerm
scoped syntax:35 smtTerm:36 " ∧ " smtTerm:35 : smtTerm
scoped syntax:30 smtTerm:31 " ∨ " smtTerm:30 : smtTerm
scoped syntax:max "¬ " smtTerm:40 : smtTerm

scoped syntax
  withPosition("if " smtTerm (colGe " then " smtTerm) (colGe " else " (colGt smtTerm)))
: smtTerm
scoped syntax "let " ident " ← " smtTerm "; " ppLine smtTerm : smtTerm

scoped syntax:50 smtTerm:51 " = " smtTerm:50 : smtTerm
scoped syntax "=[" smtTerm ", " smtTerm (", " smtTerm)* ","? "]" : smtTerm
scoped syntax:50 smtTerm:51 " ≠ " smtTerm:50 : smtTerm
scoped syntax "≠[" smtTerm ", " smtTerm (", " smtTerm)* ","? "]" : smtTerm
scoped syntax:50 smtTerm:51 " ≤ " smtTerm:50 : smtTerm
scoped syntax "≤[" smtTerm ", " smtTerm (", " smtTerm)* ","? "]" : smtTerm
scoped syntax:50 smtTerm:51 " ≥ " smtTerm:50 : smtTerm
scoped syntax "≥[" smtTerm ", " smtTerm (", " smtTerm)* ","? "]" : smtTerm
scoped syntax:50 smtTerm:51 " < " smtTerm:50 : smtTerm
scoped syntax "<[" smtTerm ", " smtTerm (", " smtTerm)* ","? "]" : smtTerm
scoped syntax:50 smtTerm:51 " > " smtTerm:50 : smtTerm
scoped syntax ">[" smtTerm ", " smtTerm (", " smtTerm)* ","? "]" : smtTerm

scoped syntax:70 smtTerm:70 " * " smtTerm:71 : smtTerm
scoped syntax:70 smtTerm:70 " /! " smtTerm:71 : smtTerm
scoped syntax:70 smtTerm:70 " /. " smtTerm:71 : smtTerm
scoped syntax:70 smtTerm:70 " /.! " smtTerm:71 : smtTerm
scoped syntax:70 smtTerm:70 " / " smtTerm:71 : smtTerm
scoped syntax:70 smtTerm:70 " % " smtTerm:71 : smtTerm
scoped syntax:65 smtTerm:65 " + " smtTerm:66 : smtTerm
scoped syntax:65 smtTerm:65 " - " smtTerm:66 : smtTerm
scoped syntax:75 "- " smtTerm : smtTerm

scoped syntax:100 smtTerm:100 group(colGt smtTerm:101) : smtTerm

scoped syntax "smt! " ppLine group(colGt smtTerm) : term

section

open Lean.Parser.Term

scoped syntax
  (("smt! " "fun ") <|> "smtFun! ")
    (ppSpace funBinder)+ optType " => " ppLine group(colGt smtTerm)
: term
scoped syntax
  "smtPred! "
    (ppSpace funBinder) optType " => " ppLine group(colGt smtTerm)
: term
scoped syntax
  "smtRel! "
    (ppSpace funBinder) (ppSpace funBinder) optType " => " ppLine group(colGt smtTerm)
: term

end

macro_rules
| `(smt! fun $[$binders]* $[ : $ty:term ]? => $t:smtTerm ) => `(
  fun $[$binders]* $[ : $ty ]? => smt! $t
)
| `(smt! fun $[$binders]* => $t:smtTerm ) => `(
  fun $[$binders]* => smt! $t
)
| `(smtFun! $[$binders]* $[ : $ty:term ]? => $t:smtTerm ) => `(
  fun $[$binders]* $[ : $ty:term ]? => smt! $t
)
| `(smtFun! $[$binders]* => $t:smtTerm ) => `(
  fun $[$binders]* => smt! $t
)
| `(smtPred! $binder:funBinder $[ : $ty:term ]? => $t:smtTerm ) => `(
  fun $binder:funBinder $[ : $ty:term ]? => smt! $t
)
| `(smtPred! $binder:funBinder => $t:smtTerm ) => `(
  fun $binder:funBinder => smt! $t
)
| `(smtRel!
  $currBinder:funBinder $nextBinder:funBinder $[ : $ty:term ]? => $t:smtTerm
) => `(
  fun $currBinder:funBinder $nextBinder:funBinder $[ : $ty:term ]? => smt! $t
)
| `(smtRel! $currBinder:funBinder $nextBinder:funBinder => $t:smtTerm ) => `(
  fun $currBinder:funBinder $nextBinder:funBinder => smt! $t
)

-- | `(smt! [| $t:term |]) => `((pure $t))
| `(smt! ![ $t:term ]) => `($t)
| `(smt! ($t:smtTerm)) => `(smt! $t)

| `(smt! false) => `(Cvc.Term.bool false)
| `(smt! true) => `(Cvc.Term.bool true)
| `(smt! $n:ident) => `(pure $n)
| `(smt! $n:name) => `(pure $n)
| `(smt! $n:num) => `(Cvc.Term.int $n)
| `(smt! - $n:num) => `(Cvc.Term.int (- $n))

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
  `( (do (← smt! $lft).equal (← smt! $rgt)) )
| `(smt! =[ $fst:smtTerm, $snd:smtTerm $[ , $tail:smtTerm ]* $[,]? ]) =>
  `( (do Cvc.Term.mkEqual #[(← smt! ($fst)), (← smt! ($snd)), $[(← smt! ($tail)) ],* ] ) )
| `(smt! $lft ≠ $rgt) =>
  `( (do (← smt! $lft).distinct (← smt! $rgt)) )
| `(smt! ≠[ $fst:smtTerm, $snd:smtTerm $[ , $tail:smtTerm ]* $[,]? ]) =>
  `( (do Cvc.Term.mkDistinct #[(← smt! ($fst)), (← smt! ($snd)), $[(← smt! ($tail)) ],* ]) )
| `(smt! $lft ≤ $rgt) =>
  `( (do (← smt! $lft).le (← smt! $rgt)) )
| `(smt! ≤[ $fst:smtTerm, $snd:smtTerm $[ , $tail:smtTerm ]* $[,]? ]) =>
  `( (do Cvc.Term.mkLe #[(← smt! ($fst)), (← smt! ($snd)), $[(← smt! ($tail)) ],* ]) )
| `(smt! $lft ≥ $rgt) =>
  `( (do (← smt! $lft).ge (← smt! $rgt)) )
| `(smt! ≥[ $fst:smtTerm, $snd:smtTerm $[ , $tail:smtTerm ]* $[,]? ]) =>
  `( (do Cvc.Term.mkGe #[(← smt! ($fst)), (← smt! ($snd)), $[(← smt! ($tail)) ],* ]) )
| `(smt! $lft < $rgt) =>
  `( (do (← smt! $lft).lt (← smt! $rgt)) )
| `(smt! <[ $fst:smtTerm, $snd:smtTerm $[ , $tail:smtTerm ]* $[,]? ]) =>
  `( (do Cvc.Term.mkLt #[(← smt! ($fst)), (← smt! ($snd)), $[(← smt! ($tail)) ],* ]) )
| `(smt! $lft > $rgt) =>
  `( (do (← smt! $lft).gt (← smt! $rgt)) )
| `(smt! >[ $fst:smtTerm, $snd:smtTerm $[ , $tail:smtTerm ]* $[,]? ]) =>
  `( (do Cvc.Term.mkGt #[(← smt! ($fst)), (← smt! ($snd)), $[(← smt! ($tail)) ],* ]) )

| `(smt! $f:smtTerm $arg:smtTerm) =>
  `( (do
    (← smt! $f).apply (← smt! $arg)
  ) )

| `(smt! $lft * $rgt) =>
  `( (do (← smt! $lft).mul (← smt! $rgt)) )
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

end Cvc.Term.Dsl
