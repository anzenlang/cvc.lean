/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Srt.Defs
import Cvc.Srt.Types
import Cvc.Srt.SrtBij
import Cvc.Srt.Extra


/-! # Smt sorts

- `Cvc.Srt.Defs`: main `Srt` type and its basic features.
- `Cvc.Srt.Types`: helper types, injection of `Srt` into `Type`.
- `Cvc.Srt.SrtBij`: injection of `Type` into `Srt`, inverse of the injection of `Srt` into `Type`.
- `Cvc.Srt.Extra`: more helpers/features building on all the modules above.

-/
