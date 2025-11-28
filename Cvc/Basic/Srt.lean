/-
Copyright (c) 2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import cvc5



namespace Cvc

namespace Srt

@[inherit_doc cvc5.SortKind]
def Kind := cvc5.SortKind

namespace Kind

local syntax "Cvc.Srt.Kind.generatePatterns!" : command
open Lean Elab Command in
elab_rules : command
| `(Cvc.Srt.Kind.generatePatterns!) =>
  let kindIdent := ``Kind |> mkIdent
  let array := #[
    (`null, ``cvc5.SortKind.NULL_SORT),
    (`abstract, ``cvc5.SortKind.ABSTRACT_SORT),
    (`array, ``cvc5.SortKind.ARRAY_SORT),
    (`bag, ``cvc5.SortKind.BAG_SORT),
    (`boolean, ``cvc5.SortKind.BOOLEAN_SORT),
    (`bitvector, ``cvc5.SortKind.BITVECTOR_SORT),
    (`datatype, ``cvc5.SortKind.DATATYPE_SORT),
    (`finite_field, ``cvc5.SortKind.FINITE_FIELD_SORT),
    (`floatingpoint, ``cvc5.SortKind.FLOATINGPOINT_SORT),
    (`function, ``cvc5.SortKind.FUNCTION_SORT),
    (`integer, ``cvc5.SortKind.INTEGER_SORT),
    (`real, ``cvc5.SortKind.REAL_SORT),
    (`reglan, ``cvc5.SortKind.REGLAN_SORT),
    (`roundingmode, ``cvc5.SortKind.ROUNDINGMODE_SORT),
    (`sequence, ``cvc5.SortKind.SEQUENCE_SORT),
    (`set, ``cvc5.SortKind.SET_SORT),
    (`string, ``cvc5.SortKind.STRING_SORT),
    (`tuple, ``cvc5.SortKind.TUPLE_SORT),
    (`nullable, ``cvc5.SortKind.NULLABLE_SORT),
    (`uninterpreted, ``cvc5.SortKind.UNINTERPRETED_SORT),
    (`last, ``cvc5.SortKind.LAST_SORT_KIND),
  ].map fun (n1, n2) => (mkIdent n1, mkIdent n2)
  for (defIdent, variantIdent) in array do
    let stx ← `(
      @[inherit_doc $variantIdent, match_pattern]
      abbrev $defIdent : $kindIdent := $variantIdent
    )
    elabCommand stx

Cvc.Srt.Kind.generatePatterns!

/-- Constructor from an unsafe sort. -/
def ofUnsafe : cvc5.SortKind → Srt.Kind := id

/-- Conversion to an unsafe sort. -/
def toUnsafe : Srt.Kind → cvc5.SortKind := id

/-- String representation. -/
protected def toString : Srt.Kind → String := cvc5.SortKind.toString

instance : ToString Srt.Kind := ⟨Kind.toString⟩

end Kind

end Srt
