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

This section gives a brief overview of cvc.lean's main features: term management, solver
interactions, and symbols/state/system extra features.



{include 1 Manual.Chap1Overview.Sec1Terms}

{include 1 Manual.Chap1Overview.Sec2Solver}

{include 1 Manual.Chap1Overview.Sec3Symbols}
