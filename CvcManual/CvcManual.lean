/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import VersoManual

import CvcManual.Overview
import CvcManual.Env
import CvcManual.Sorts
import CvcManual.Terms
import CvcManual.Smt
import CvcManual.Datatypes
import CvcManual.Solver
import CvcManual.Proofs

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

open CvcManual

set_option pp.rawOnError true
set_option verso.docstring.allowMissing true

#doc (Manual) "Cvc.lean -- High-Level API for cvc5" =>
%%%
authors := ["Adrien Champion"]
shortTitle := "Cvc.lean user manual"
%%%


_Cvc.lean_ is a high-level Lean 4 API for the [cvc5 SMT solver][cvc5], built on top of the [lean-cvc5 Lean library][lean-cvc5]. It adds a lot of quality of life features and strives to provide strong static guarantees. The following sections of this manual present the library in detail.

{ref "overview"}[The Overview section] showcases various features of cvc.lean to give an overview for newcomers to survey quickly. The rest of this document goes over the technical details needed to understand and use cvc.lean properly.

{include 1 CvcManual.Overview}

{include 1 CvcManual.Env}

{include 1 CvcManual.Sorts}

{include 1 CvcManual.Terms}

{include 1 CvcManual.Smt}

{include 1 CvcManual.Datatypes}

{include 1 CvcManual.Solver}

{include 1 CvcManual.Proofs}


# Index
%%%
number := false
tag := "index"
%%%

{theIndex}

[cvc5]: (https://cvc5.github.io)
[lean-cvc5]: (https://github.com/abdoo8080/lean-cvc5)
