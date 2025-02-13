/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Safe.Smt



namespace Cvc.Term



declare_syntax_cat smterm


-- scoped syntax "[|" term "|]" : smterm
-- scoped syntax "![" term "]" : smterm

scoped syntax "(" smterm ")" : smterm

scoped syntax ident : smterm
scoped syntax name : smterm
scoped syntax num : smterm

scoped syntax:25 smterm:26 " → " smterm:25 : smterm
scoped syntax:35 smterm:36 " ∧ " smterm:35 : smterm
scoped syntax:30 smterm:31 " ∨ " smterm:30 : smterm
scoped syntax:max "¬ " smterm:40 : smterm

scoped syntax
  withPosition("if " (colGt smterm) " then " (colGt smterm) " else " (colGt smterm))
: smterm
scoped syntax "let " ident " ← " smterm "; " ppLine smterm : smterm

scoped syntax:50 smterm:51 " = " smterm:50 : smterm
scoped syntax:50 smterm:51 " ≠ " smterm:50 : smterm
scoped syntax:50 smterm:51 " ≤ " smterm:50 : smterm
scoped syntax:50 smterm:51 " ≥ " smterm:50 : smterm
scoped syntax:50 smterm:51 " < " smterm:50 : smterm
scoped syntax:50 smterm:51 " > " smterm:50 : smterm

scoped syntax:70 smterm:70 " * " smterm:71 : smterm
scoped syntax:70 smterm:70 " /! " smterm:71 : smterm
scoped syntax:70 smterm:70 " /. " smterm:71 : smterm
scoped syntax:70 smterm:70 " /.! " smterm:71 : smterm
scoped syntax:70 smterm:70 " / " smterm:71 : smterm
scoped syntax:70 smterm:70 " % " smterm:71 : smterm
scoped syntax:65 smterm:65 " + " smterm:66 : smterm
scoped syntax:65 smterm:65 " - " smterm:66 : smterm
scoped syntax:75 "- " smterm : smterm

scoped syntax:100 smterm:100 group(colGt smterm:101 (smterm:101)*) : smterm

scoped syntax "smt! " ppLine group(colGt smterm) : term

section

open Lean.Parser.Term

scoped syntax
  (("smt! " "fun ") <|> "smtFun! ") (ppSpace funBinder)+ optType
    " => " ppLine group(colGt smterm) : term
scoped syntax
  "smtPred! " (ppSpace funBinder) optType
    " => " ppLine group(colGt smterm) : term
scoped syntax
  "smtRel!" (ppSpace funBinder) (ppSpace funBinder) optType
    " => " ppLine group(colGt smterm) : term

end

macro_rules
| `(smt! fun $[$binders]* $[ : $ty:term ]? => $t:smterm ) => `(
  fun $[$binders]* $[ : $ty ]? => smt! $t
)
| `(smt! fun $[$binders]* => $t:smterm ) => `(
  fun $[$binders]* => smt! $t
)
| `(smtFun! $[$binders]* $[ : $ty:term ]? => $t:smterm ) => `(
  fun $[$binders]* $[ : $ty:term ]? => smt! $t
)
| `(smtFun! $[$binders]* => $t:smterm ) => `(
  fun $[$binders]* => smt! $t
)
| `(smtPred! $binder:funBinder $[ : $ty:term ]? => $t:smterm ) => `(
  fun $binder:funBinder $[ : $ty:term ]? => smt! $t
)
| `(smtPred! $binder:funBinder => $t:smterm ) => `(
  fun $binder:funBinder => smt! $t
)
| `(smtRel! $currBinder:funBinder $nextBinder:funBinder $[ : $ty:term ]? => $t:smterm ) => `(
  fun $currBinder:funBinder $nextBinder:funBinder $[ : $ty:term ]? => smt! $t
)
| `(smtRel! $currBinder:funBinder $nextBinder:funBinder => $t:smterm ) => `(
  fun $currBinder:funBinder $nextBinder:funBinder => smt! $t
)

-- | `(smt! [| $t:term |]) => `((pure $t))
-- | `(smt! ![ $t:term ]) => `($t)
| `(smt! ($t:smterm)) => `(smt! $t)

| `(smt! $f:smterm $arg:smterm $[ $tail:smterm ]*) =>
  `( (do
    (← smt! $f).apply #[ (← smt! $arg), $[ (← smt! $tail) ],* ]
  ) )

| `(smt! false) => `(Cvc.Term.mkBool false)
| `(smt! true) => `(Cvc.Term.mkBool true)
| `(smt! $n:ident) => `(pure $n)
| `(smt! $n:name) => `(pure $n)
| `(smt! $n:num) => `(Cvc.Term.mkInt $n)
| `(smt! - $n:num) => `(Cvc.Term.mkInt (- $n))

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
  `( (do Cvc.Term.mkDistinct #[(← smt! $lft), (← smt! $rgt)]) )
| `(smt! $lft ≤ $rgt) =>
  `( (do (← smt! $lft).le (← smt! $rgt)) )
| `(smt! $lft ≥ $rgt) =>
  `( (do (← smt! $lft).ge (← smt! $rgt)) )
| `(smt! $lft < $rgt) =>
  `( (do (← smt! $lft).lt (← smt! $rgt)) )
| `(smt! $lft > $rgt) =>
  `( (do (← smt! $lft).gt (← smt! $rgt)) )

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

end Cvc.Term



namespace Cvc.Safe.Term

declare_syntax_cat safesmterm


-- scoped syntax "[|" term "|]" : safesmterm
scoped syntax "![" term "]" : safesmterm

scoped syntax "(" safesmterm ")" : safesmterm

scoped syntax ident : safesmterm
scoped syntax name : safesmterm
scoped syntax num : safesmterm

scoped syntax:25 safesmterm:26 " → " safesmterm:25 : safesmterm
scoped syntax:35 safesmterm:36 " ∧ " safesmterm:35 : safesmterm
scoped syntax:30 safesmterm:31 " ∨ " safesmterm:30 : safesmterm
scoped syntax:max "¬ " safesmterm:40 : safesmterm

scoped syntax
  withPosition("if " safesmterm (colGe " then " safesmterm) (colGe " else " (colGt safesmterm)))
: safesmterm
scoped syntax "let " ident " ← " safesmterm "; " ppLine safesmterm : safesmterm

scoped syntax:50 safesmterm:51 " = " safesmterm:50 : safesmterm
scoped syntax:50 safesmterm:51 " ≠ " safesmterm:50 : safesmterm
scoped syntax:50 safesmterm:51 " ≤ " safesmterm:50 : safesmterm
scoped syntax:50 safesmterm:51 " ≥ " safesmterm:50 : safesmterm
scoped syntax:50 safesmterm:51 " < " safesmterm:50 : safesmterm
scoped syntax:50 safesmterm:51 " > " safesmterm:50 : safesmterm

scoped syntax:70 safesmterm:70 " * " safesmterm:71 : safesmterm
scoped syntax:70 safesmterm:70 " /! " safesmterm:71 : safesmterm
scoped syntax:70 safesmterm:70 " /. " safesmterm:71 : safesmterm
scoped syntax:70 safesmterm:70 " /.! " safesmterm:71 : safesmterm
scoped syntax:70 safesmterm:70 " / " safesmterm:71 : safesmterm
scoped syntax:70 safesmterm:70 " % " safesmterm:71 : safesmterm
scoped syntax:65 safesmterm:65 " + " safesmterm:66 : safesmterm
scoped syntax:65 safesmterm:65 " - " safesmterm:66 : safesmterm
scoped syntax:75 "- " safesmterm : safesmterm

scoped syntax:100 safesmterm:100 group(colGt safesmterm:101) : safesmterm

scoped syntax "smt! " ppLine group(colGt safesmterm) : term

section

open Lean.Parser.Term

scoped syntax
  (("smt! " "fun ") <|> "smtFun! ")
    (ppSpace funBinder)+ optType " => " ppLine group(colGt safesmterm)
: term
scoped syntax
  "smtPred! "
    (ppSpace funBinder) optType " => " ppLine group(colGt safesmterm)
: term
scoped syntax
  "smtRel! "
    (ppSpace funBinder) (ppSpace funBinder) optType " => " ppLine group(colGt safesmterm)
: term

end

macro_rules
| `(smt! fun $[$binders]* $[ : $ty:term ]? => $t:safesmterm ) => `(
  fun $[$binders]* $[ : $ty ]? => smt! $t
)
| `(smt! fun $[$binders]* => $t:safesmterm ) => `(
  fun $[$binders]* => smt! $t
)
| `(smtFun! $[$binders]* $[ : $ty:term ]? => $t:safesmterm ) => `(
  fun $[$binders]* $[ : $ty:term ]? => smt! $t
)
| `(smtFun! $[$binders]* => $t:safesmterm ) => `(
  fun $[$binders]* => smt! $t
)
| `(smtPred! $binder:funBinder $[ : $ty:term ]? => $t:safesmterm ) => `(
  fun $binder:funBinder $[ : $ty:term ]? => smt! $t
)
| `(smtPred! $binder:funBinder => $t:safesmterm ) => `(
  fun $binder:funBinder => smt! $t
)
| `(smtRel!
  $currBinder:funBinder $nextBinder:funBinder $[ : $ty:term ]? => $t:safesmterm
) => `(
  fun $currBinder:funBinder $nextBinder:funBinder $[ : $ty:term ]? => smt! $t
)
| `(smtRel! $currBinder:funBinder $nextBinder:funBinder => $t:safesmterm ) => `(
  fun $currBinder:funBinder $nextBinder:funBinder => smt! $t
)

-- | `(smt! [| $t:term |]) => `((pure $t))
| `(smt! ![ $t:term ]) => `($t)
| `(smt! ($t:safesmterm)) => `(smt! $t)

| `(smt! false) => `(Cvc.Safe.Term.mkBool false)
| `(smt! true) => `(Cvc.Safe.Term.mkBool true)
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

| `(smt! $f:safesmterm $arg:safesmterm) =>
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

end Cvc.Safe.Term
