/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Spec.Decl



/-! # String specification

The full SMT-LIB string theory, including the operators
crossing over to `Int` and to regular expressions.
-/
namespace Cvc public section



/-! ## Predicates -/

/-- Containment. -/
op% strContains (s sub : string) : bool := STRING_CONTAINS

/-- Prefix predicate: whether the first string is a prefix of the second. -/
op% strPrefix (pre s : string) : bool := STRING_PREFIX

/-- Suffix predicate: whether the first string is a suffix of the second. -/
op% strSuffix (suf s : string) : bool := STRING_SUFFIX

/-- Whether the string is a single digit, `"0"` through `"9"`. -/
op% strIsDigit (s : string) : bool := STRING_IS_DIGIT

/-- Strict lexicographic comparison over code points. -/
op% strLt (lft rgt : string) : bool := STRING_LT

/-- Lexicographic comparison over code points. -/
op% strLe (lft rgt : string) : bool := STRING_LEQ

/-- Regular-expression membership. -/
op% strInRegex (s : string) (re : regex) : bool := STRING_IN_REGEXP



/-! ## The rest of the theory -/

/-- Concatenation. -/
op% strConcat (lft rgt : string) : string := STRING_CONCAT nary

/-- Length. -/
op% strLength (s : string) : int := STRING_LENGTH

/-- The sub-string of the given length, starting at the given index. -/
op% strSubstr (s : string) (idx len : int) : string := STRING_SUBSTR

/-- The one-character string at an index, or the empty string if out of bounds. -/
op% strCharAt (s : string) (idx : int) : string := STRING_CHARAT

/-- Index of the first occurrence of a sub-string at or after a starting index. -/
op% strIndexof (s sub : string) (start : int) : int := STRING_INDEXOF

/-- Index of the first match of a regular expression at or after a starting index. -/
op% strIndexofRe (s : string) (re : regex) (start : int) : int := STRING_INDEXOF_RE

/-- Replaces the first occurrence of a sub-string. -/
op% strReplace (s pat repl : string) : string := STRING_REPLACE

/-- Replaces every occurrence of a sub-string. -/
op% strReplaceAll (s pat repl : string) : string := STRING_REPLACE_ALL

/-- Replaces the first match of a regular expression. -/
op% strReplaceRe (s : string) (re : regex) (repl : string) : string := STRING_REPLACE_RE

/-- Replaces every match of a regular expression. -/
op% strReplaceReAll (s : string) (re : regex) (repl : string) : string := STRING_REPLACE_RE_ALL

/-- Reversal. -/
op% strRev (s : string) : string := STRING_REV

/-- Replaces the sub-string starting at an index. -/
op% strUpdate (s : string) (idx : int) (repl : string) : string := STRING_UPDATE

/-- Conversion to lower case. -/
op% strToLower (s : string) : string := STRING_TO_LOWER

/-- Conversion to upper case. -/
op% strToUpper (s : string) : string := STRING_TO_UPPER

/-- Code point of a one-character string, or `-1` otherwise. -/
op% strToCode (s : string) : int := STRING_TO_CODE

/-- The one-character string with the given code point, or the empty string if out of range. -/
op% strFromCode (code : int) : string := STRING_FROM_CODE

/-- Value of a string of digits, or `-1` if it is not one. -/
op% strToInt (s : string) : int := STRING_TO_INT

/-- Decimal representation of a non-negative integer, or the empty string otherwise. -/
op% strFromInt (arg : int) : string := STRING_FROM_INT

/-- The regular expression matching exactly the given string. -/
op% strToRegex (s : string) : regex := STRING_TO_REGEXP

/-! ## Constructors -/

/-- A string literal. -/
op% mkString (s :! String) (useEscapes :! Bool) : string := CONST_STRING tm mkString
