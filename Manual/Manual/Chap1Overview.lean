/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import VersoManual

import Manual.Meta.Lean

import Manual.Chap1Overview.Sec1Terms
import Manual.Chap1Overview.Sec2Solver
import Manual.Chap1Overview.Sec3Symbols
import Manual.Chap1Overview.Sec4Erased

import Cvc

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Manual

open Cvc

set_option pp.rawOnError true


#doc (Manual) "Overview" =>

%%%
tag := "chapIntro"
%%%

This chapter gives a brief overview of cvc.lean's main features.

- {ref "chapOverview_terms"}[Terms] discusses strongly-typed terms and the term DSL;

- {ref "chapOverview_solver"}[Solver] presents basic solver interactions;

- {ref "chapOverview_symbols"}[Symbols/States/Systems] showcases a high-level part of cvc.lean that
  serves both as
  - an actual API for symbol/state/transition system representation and model-checking;
  - an example of the kind of high-level features one can build on top of cvc.lean.

- {ref "chapOverview_erased"}[Type-erased] surveys the _erased_ facet of cvc.lean which relaxes
  strong-typing so that terms/symbols/states/systems can be used without knowing at compile-time
  the type of the symbols manipulated. This is particularly useful when parsing end-user-defined
  terms/symbols/states/systems.



{include 1 Manual.Chap1Overview.Sec1Terms}

{include 1 Manual.Chap1Overview.Sec2Solver}

{include 1 Manual.Chap1Overview.Sec3Symbols}

{include 1 Manual.Chap1Overview.Sec4Erased}
