/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import CvcTest.Init

namespace Cvc.Tactic.Test

scoped syntax docComment ? "#test " command : command

macro_rules
| `(command| $outputComment:docComment #test $cmd:command) => `(
  $outputComment:docComment
  #guard_msgs in $cmd
)
| `(command| #test $cmd:command) => `(
  /-- info: -/
  #test $cmd
)
end Test