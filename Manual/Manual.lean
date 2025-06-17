/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import VersoManual

import Manual.Meta.Lean

-- This is a chapter that's included
import Manual.Chap1Overview

-- This gets access to most of the manual genre (which is also useful for textbooks)
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Genre.Manual.InlineLean


open Manual

set_option pp.rawOnError true



#doc (Manual) "Cvc.lean User Manual" =>

%%%
authors := ["Adrien Champion"]
draft := true
%%%

Welcome to the [cvc.lean][cvc.lean] user manual. The code documentation is available at
[anzenlang.io/cvc.lean][docs].

Cvc.lean is a high-level API for the [cvc5 SMT solver][cvc5] written by [Adrien Champion][adrien]
from [anzenlang][azn] for the cvc5 team in collaboration with [Cesare Tinelli][cesare] at
[the University of Iowa][uiowa].

This library is built on [lean-cvc5][lean-cvc5] and exposes cvc5's terms, solver,
term/solver-related functions, and adds (many) more (strongly-typed) features on top such as
lean syntax extensions for natural term-construction and symbol/state structures, as well as
a *transition system* API equipped with a `k`-induction engine.

This user manual is *not* an introduction to SMT solvers. It assumes readers are familiar with the
basics of SMT solving and of the [SMT-LIB standard][smtlib].

[docs]: https://www.anzenlang.io/cvc.lean/doc/Cvc.html
[cvc.lean]: https://github.com/anzenlang/cvc.lean
[lean-cvc5]: https://github.com/abdoo8080/lean-cvc5
[cvc5]: https://cvc5.github.io
[azn]: https://www.anzenlang.io
[adrien]: https://github.com/AdrienChampion
[uiowa]: https://uiowa.edu
[cesare]: https://homepage.cs.uiowa.edu/~tinelli
[smtlib]: https://smt-lib.org

{include 1 Manual.Chap1Overview}
