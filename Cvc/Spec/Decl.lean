/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public meta import Lean.Elab.Command

public import Cvc.Spec.Defs
import all Cvc.Spec.Defs
-- needed so that `op%` can check the named `cvc5.Kind` constructor exists
public import cvc5



/-! # The `op%` specification command

`op%` declares one entry of the term-creation specification. An entry is written in the *typed*
form and registered in `Cvc.opSpecExt`; nothing is generated at the declaration site.

```lean
/-- Binary conjunction. -/
op% and (lft rgt : bool) : bool := AND unit true

/-- Binary equality. -/
op% equal {α} (lft rgt : α) : bool := EQUAL unit true

/-- Binary addition. -/
op% add {α : IsArith} (lft rgt : α) : α := ADD unit 0

/-- Binary subtraction. -/
op% sub {α : IsArith} (lft rgt : α) : α := SUB nary

/-- Bit-vector concatenation. -/
op% bvConcat {n m : size} (lft : bitVec n) (rgt : bitVec m) : bitVec (n + m) := BITVECTOR_CONCAT
```

Binders are `{α}` for a plain type variable, `{α : Class, …}` for one constrained by refinement
classes, and `{n : size}` for a size variable. Square brackets ahead of the binders declare
*operator indices*, the `Nat`s SMT-LIB writes as `(_ extract hi lo)`:

```lean
/-- The bit range `[lo, hi]`, both bounds included. -/
op% bvExtract [hi lo] {n : size} (bv : bitVec n) : bitVec (hi - lo + 1) := BITVECTOR_EXTRACT
```

Indices become explicit `Nat` arguments ahead of the term arguments and may appear in the
result's sort; size variables stay implicit and are inferred from the arguments.

Sort shapes reuse Lean's `term` syntax and are interpreted structurally, so no new tokens are
reserved: an application head names a shape constructor (`bitVec`, `float`, `finiteField`, `seq`,
`set`, `bag`, `array`, `fn`), a bare identifier is either a sort atom (`bool`, `int`, `real`,
`string`, `regex`, `roundingMode`) or a variable.

The trailing `nary` generates the `N` variant, and `unit <literal>` generates both `N` and `N'`,
the latter defaulting on zero- and one-element arrays.

Syntax categories introduced here use `(behavior := symbol)` so that their leading identifiers are
not reserved as keywords for every downstream module.
-/
namespace Cvc public meta section

open Lean Elab Command



/-- Operator indices, written like SMT-LIB's `(_ extract hi lo)`. -/
syntax opIndices := "[" ident+ "]"

/-- Binder for a type or size variable. -/
syntax opBinder := "{" ident+ (" : " ident,+)? "}"

/-- Group of arguments sharing a sort shape. -/
syntax opArgGroup := "(" ident+ " : " term ")"

/-- Group of value parameters sharing a Lean type, written `(name :! Type)`. -/
syntax opValGroup := atomic("(" ident+ " :! ") ident ")"

/-- N-ary generation policy.

Declared with `behavior := symbol` so that the leading identifiers are not reserved as keywords
globally, which would shadow the `nary`/`unit` field names.
-/
declare_syntax_cat opNary (behavior := symbol)

/-- Generate the `N` variant, which takes a term array with at least two elements. -/
syntax " nary" : opNary
/-- As `nary`, naming the variant, for when `<id>N` is not the right name. -/
syntax " naryAs " ident : opNary
/-- Generate the `N` and `N'` variants, the latter defaulting on 0- and 1-element arrays. -/
syntax " unit " term : opNary

/-- How the term is built, when applying its kind is not how.

Declared with `behavior := symbol` so that `tm` is not reserved as a keyword globally.
-/
declare_syntax_cat opBuild (behavior := symbol)

/-- Build the term with the named `TermManager` method rather than by applying the kind. -/
syntax " tm " ident : opBuild
/-- As `tm`, naming the shape whose sort the method takes, for the methods that do not take the
sort of the term they build. -/
syntax " tmSortOf " ident term : opBuild

/-- Surface notation for the `smt!` DSL.

`infixl`/`infixr`/`prefix` are already Lean tokens, so naming them here reserves nothing new.
-/
declare_syntax_cat opNotation (behavior := symbol)

/-- Left-associative infix notation, at the given precedence. -/
syntax " infixl " str num : opNotation
/-- Right-associative infix notation, at the given precedence. -/
syntax " infixr " str num : opNotation
/-- Prefix notation, at the given rule and argument precedences. -/
syntax " prefix " str num num : opNotation

@[inherit_doc Cvc.OpSpec]
syntax (name := opStx)
  (docComment)?
  "op% " ident (ppSpace opIndices)? (ppSpace opBinder)* (ppSpace opValGroup)*
    (ppSpace opArgGroup)* " : " term " := " ident (opBuild)? (opNotation)? (opNary)?
: command



/-- Sort atoms, by the identifier naming them in `op%` syntax. -/
def shapeAtom? : Name → Option Shape
  | `bool => some .bool
  | `int => some .int
  | `real => some .real
  | `string => some .string
  | `regex => some .regex
  | `roundingMode => some .roundingMode
  | _ => none

/-- Interprets `term` syntax as a size expression. -/
partial def toSize (stx : Syntax) : CommandElabM SizeExpr := do
  match stx with
  | `($n:num) => return .lit n.getNat
  | `($lft + $rgt) => return .add (← toSize lft) (← toSize rgt)
  | `($lft - $rgt) => return .sub (← toSize lft) (← toSize rgt)
  | `($lft * $rgt) => return .mul (← toSize lft) (← toSize rgt)
  | `(($inner)) => toSize inner
  | `($id:ident) =>
    -- `arity` is reserved: it denotes how many term arguments the operator was applied to
    if id.getId == `arity then return .arity else return .var id.getId
  | _ =>
    throwErrorAt stx
      "expected a size expression: a numeral, a variable, or a sum, difference or product"

/-- Interprets `term` syntax as a sort shape. -/
partial def toShape (stx : Syntax) : CommandElabM Shape := do
  match stx with
  | `(($inner)) => toShape inner
  | `($f:ident $args*) =>
    match f.getId, args with
    | `bitVec, #[w] => return .bitVec (← toSize w)
    | `float, #[e, s] => return .float (← toSize e) (← toSize s)
    | `finiteField, #[s] => return .finiteField (← toSize s)
    | `seq, #[e] => return .seq (← toShape e)
    | `set, #[e] => return .set (← toShape e)
    | `bag, #[e] => return .bag (← toShape e)
    | `array, #[i, e] => return .array (← toShape i) (← toShape e)
    | `fn, #[d, c] => return .fn (← toShape d) (← toShape c)
    | head, _ => throwErrorAt stx s!"unknown shape constructor `{head}`, or wrong arity"
  | `($id:ident) =>
    if let some atom := shapeAtom? id.getId then return atom else return .var id.getId
  | _ => throwErrorAt stx "expected a sort shape"

/-- Interprets `term` syntax as the unit element of an n-ary operator. -/
def toNaryUnit (stx : Syntax) : CommandElabM NaryUnit := do
  match stx with
  | `(true) => return .bool true
  | `(false) => return .bool false
  | `($n:num) => return .int n.getNat
  | _ => throwErrorAt stx "expected `true`, `false`, or a numeral"



@[command_elab opStx]
def elabOpStx : CommandElab
  | `(
    $[ $doc?:docComment ]?
    op% $id $[ [ $indexIds* ] ]? $[ { $binderIds* $[ : $binderClasses?,* ]? } ]*
      $[ ( $valIds* :! $valTys ) ]* $[ ( $argIds* : $argShapes ) ]*
      : $ret := $kind $[ $build?:opBuild ]? $[ $notation?:opNotation ]?
        $[ $nary?:opNary ]?
  ) => do
    let indices := match indexIds with
      | none => #[]
      | some ids => ids.map (·.getId)
    let mut tyVars := #[]
    let mut sizeVars := #[]
    for ids in binderIds, classes? in binderClasses? do
      let classes := match classes? with
        | none => #[]
        | some cs => cs.getElems.map (·.getId)
      if classes == #[`size] then
        sizeVars := sizeVars ++ ids.map (·.getId)
      else
        tyVars := tyVars ++ ids.map (fun id => { name := id.getId, classes : TyVar })

    let mut valArgs := #[]
    for ids in valIds, ty in valTys do
      valArgs := valArgs ++ ids.map (fun id => { name := id.getId, type := ty.getId : ValArg })

    let mut args := #[]
    for ids in argIds, shapeStx in argShapes do
      let shape ← toShape shapeStx
      args := args ++ ids.map (fun id => { name := id.getId, shape : Arg })

    let retShape ← toShape ret

    let mut naryName : Option Name := none
    let nary : Nary ← match nary? with
      | none => pure Nary.never
      | some stx => match stx with
        | `(opNary| nary) => pure Nary.array
        | `(opNary| naryAs $nm:ident) => do
          naryName := some nm.getId
          pure Nary.array
        | `(opNary| unit $u) => Nary.arrayWithUnit <$> toNaryUnit u
        | _ => throwErrorAt stx "expected `nary`, `naryAs <name>` or `unit <literal>`"

    let mut sortArg : Option Shape := none
    let tmFn : Option Name ← match build? with
      | none => pure none
      | some stx => match stx with
        | `(opBuild| tm $fn:ident) => pure (some fn.getId)
        | `(opBuild| tmSortOf $fn:ident $shape) => do
          sortArg := some (← toShape shape)
          pure (some fn.getId)
        | _ => throwErrorAt stx "expected `tm <method>` or `tmSortOf <method> <shape>`"

    let smtNotation : Notation ← match notation? with
      | none => pure Notation.none
      | some stx => match stx with
        | `(opNotation| infixl $s:str $p:num) =>
          pure (Notation.inf s.getString p.getNat .left)
        | `(opNotation| infixr $s:str $p:num) =>
          pure (Notation.inf s.getString p.getNat .right)
        | `(opNotation| prefix $s:str $p:num $a:num) =>
          pure (Notation.pref s.getString p.getNat a.getNat)
        | _ => throwErrorAt stx "expected `infixl`, `infixr` or `prefix`"

    let kindName := `cvc5 ++ `Kind ++ kind.getId
    unless (← getEnv).contains kindName do
      throwErrorAt kind s!"`{kindName}` is not a constructor of `cvc5.Kind`"

    let doc ← match doc? with
      | none => pure s!"Term constructor for `cvc5.Kind.{kind.getId}`."
      | some d => do pure (← getDocStringText d).trimAscii.toString

    let spec : OpSpec := {
      id := id.getId, kind := kind.getId, tmFn, sortArg, doc, tyVars, sizeVars, indices
      valArgs, args
      ret := retShape, nary, naryName, smtNotation
      declaredIn := ← getMainModule, order := ← opSpecCount
    }

    for index in indices do
      if sizeVars.contains index then
        throwErrorAt id s!"`{index}` is declared both as an operator index and a size variable"
    unless indices.isEmpty || spec.nary matches .never do
      throwErrorAt id "an indexed operator cannot also have n-ary variants"

    unless spec.unboundRetVars.isEmpty || spec.tmFn.isSome do
      throwErrorAt ret s!"\
        result mentions type variable(s) {spec.unboundRetVars} bound by no argument, so the \
        untyped signature could not be derived by erasure; a constructor built with `tm` may do \
        this, since it takes its own sort"

    registerOpSpec spec
  | _ => throwUnsupportedSyntax
