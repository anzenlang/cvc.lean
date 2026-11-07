/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public meta import Lean.Elab.Command

public import Cvc.Basic



/-! # Generating a symbols structure

`structure.symbols` writes the boilerplate a `Symbols` instance needs. A user states the symbols
they want and the Lean type each denotes:

```lean
structure.symbols MySymbols where
  /-- Whether the thing is on. -/
  isOn : Bool
  count : Int
```

and what is generated is the structure the `Symbols` class actually wants — parameterized by the
`Wrap`, with every field wrapped in it — plus one alias per `Symbols.Sig` type (`Idents`, `Terms`,
`Values`, …), the `idents` naming each symbol, and the instance:

```lean
structure MySymbols (W : Symbols.Wrap) where
  isOn : W Bool
  count : W Int
```

**A symbol's name is its field's name**, as a string. `declare`, `getValues` and `findCex` are
generic over the `Sig`, so nothing beyond the instance is needed for them.

This module holds what both layers share. Each layer declares its own `scoped` spelling of the
command, so `open Cvc.Untyped` selects the sort-erased one exactly as it selects `smt!`.
-/
namespace Cvc.Ext public meta section

open Lean Elab Command



/-- Names generated or reached beside a symbols structure other than its aliases, which a symbol
therefore cannot be called. -/
def symbolsReserved : Array Name :=
  #[`idents, `mapM, `foldM, `declare, `declareIn, `getValues, `findCex]

/-- The aliases of `Symbols.Sig` both layers generate beside a symbols structure, with the same
parameters in both, each with whether it takes the scope. A layer's own aliases are its `extras`. -/
def symbolsSharedAliases : Array (Name × Bool) :=
  #[(`Idents, false), (`Values, false), (`ValuesAt, false),
    (`Terms, true), (`TermsAt, true), (`BVars, true), (`ValueTerms, true), (`ValueTermsAt, true)]

/-- The body of a generated `foldM syms acc f`: `f acc syms.a >>= fun acc => f acc syms.b >>= …`,
over the given fields in order. -/
def foldChain [Monad m] [MonadQuotation m] (fields : Array Name) : m (TSyntax `term) := do
  let mut body ← `(pure acc)
  for f in fields.reverse do
    body ← `(f acc syms.$(mkIdent f):ident >>= fun acc => $body)
  return body
-- A chain of binds rather than a `do` block, since a `do` whose items are all spliced elaborates
-- as empty.

open Lean.Parser.Command in
/-- `structure <id> (<w> : <wrap>) where <binders>`, with `doc?` as its doc comment. -/
def mkSymbolsStructure (doc? : Option Syntax) (id w wrap : Syntax) (binders : Array Syntax)
: Syntax :=
  let nulls := Array.replicate 7 mkNullNode
  let mods := mkNode ``declModifiers (nulls.set! 0 (mkNullNode doc?.toArray))
  let binder := mkNode ``Lean.Parser.Term.explicitBinder
    #[mkAtom "(", mkNullNode #[w], mkNullNode #[mkAtom ":", wrap], mkNullNode, mkAtom ")"]
  mkNode ``Lean.Parser.Command.declaration #[mods, mkNode ``«structure» #[
    mkNode ``structureTk #[mkAtom "structure"],
    mkNode ``declId #[id, mkNullNode],
    mkNode ``Lean.Parser.Command.optDeclSig #[mkNullNode #[binder], mkNullNode],
    mkNullNode,
    mkNullNode #[mkAtom "where", mkNullNode, mkNode ``structFields #[mkNullNode binders]],
    mkNode ``optDeriving #[mkNullNode]]]
-- Assembled node by node: a quotation cannot splice a variable number of fields into
-- `structFields`, that position being a `manyIndent`, where an antiquotation is read as the *name*
-- of a single field. Two shapes have to be right and are easy to get wrong — `structFields` holds
-- its binders in a null node rather than as direct children, and `declModifiers`' first slot is a
-- null node holding the doc comment, empty when there is none.

/-- One field, rebuilt with its type wrapped in `w`.

Everything the writer wrote — the doc comment, the name, the source position — is carried over
untouched; only the type is replaced, by `w` applied to it.
-/
def wrapSymbolsField (w : Ident) (field : TSyntax ``Lean.Parser.Command.structSimpleBinder)
: CommandElabM Syntax := do
  let stx := field.raw
  let sig := stx[2]
  unless sig[0].getNumArgs == 0 do
    throwErrorAt field "a symbol takes no parameters: write `name : Type`"
  unless sig[1].getNumArgs == 1 do
    throwErrorAt field "a symbol needs a type: write `name : Type`"
  let spec := sig[1][0]
  let ty : TSyntax `term := ⟨spec[1]⟩
  let ty' ← `($w $ty)
  return stx.setArg 2 (sig.setArg 1 (mkNullNode #[spec.setArg 1 ty'.raw]))

/-- Emits a symbols structure and everything generated beside it.

`root` is the layer's namespace, and `extras` the aliases only that layer has, beside the shared
`symbolsSharedAliases`, each with whether it takes the scope. Every alias is `Symbols.Sig.<name>`
applied to the structure, so its own parameters — a sort, a depth — stay those of the definition.
-/
def elabSymbols (root : Name) (extras : Array (Name × Bool))
  (doc? : Option (TSyntax ``Lean.Parser.Command.docComment)) (id : Ident)
  (fields : Array (TSyntax ``Lean.Parser.Command.structSimpleBinder))
: CommandElabM Unit := do
  let omegaId := mkIdent ``Ω
  let omegaArg ← `(bracketedBinder| [$omegaId])
  let aliases := symbolsSharedAliases ++ extras
  let reserved := symbolsReserved ++ aliases.map (·.1)
  let mut names := Array.mkEmpty fields.size
  for field in fields do
    let name := field.raw[1].getId
    if reserved.contains name then
      throwErrorAt field.raw[1]
        s!"`{name}` is generated beside a symbols structure, so a symbol cannot be called that"
    names := names.push name

  let w := mkIdent `W
  let wrap := mkIdent (root ++ `Symbols.Wrap)
  let binders ← fields.mapM (wrapSymbolsField w)
  elabCommand (mkSymbolsStructure (doc?.map (·.raw)) id w wrap binders)

  let ns := id.getId
  let identArgs : Array (TSyntax `term) := names.map (Syntax.mkStrLit ·.toString)
  let mapArgs ← names.mapM fun f => `(← f syms.$(mkIdent f):ident)
  let foldBody ← foldChain names
  let mut cmds := #[]
  for (name, omega) in aliases do
    let args := if omega then #[omegaArg] else #[]
    let sigName := mkIdent (root ++ `Symbols.Sig ++ name)
    -- applied with `@`, which fills no default: without it, `Fun2At`'s optional `k'` would be fixed
    -- to its default `k + 1` here, rather than left in the alias's type for its users to fill
    let body ← if omega then `(@$sigName _ $id) else `(@$sigName $id)
    cmds := cmds.push
      (← `(command| @[inherit_doc $sigName] abbrev $(mkIdent (ns ++ name)) $[$args]* := $body))
  let identsId := mkIdent (ns ++ `idents)
  let IdentsId := mkIdent (ns ++ `Idents)
  cmds := cmds.push (← `(command|
    /-- The symbols' identifiers: each symbol is named after its field. -/
    def $identsId : $(IdentsId) := ⟨$identArgs,*⟩))
  cmds := cmds.push (← `(command| instance : $(mkIdent (root ++ `Symbols)) $id where
    idents _ := $identsId
    mapM syms f := return ⟨$mapArgs,*⟩
    foldM syms acc f := $foldBody))
  for cmd in cmds do elabCommand cmd

end
