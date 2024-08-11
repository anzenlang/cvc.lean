/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Init.Logic

import CvcTest.Init



namespace Cvc.Test

open Logic

/-- info: -/
#guard_msgs in #eval do
  assertEq "LIA"  lia.toSmtLib
  assertEq "LRA"  lra.toSmtLib
  assertEq "LIRA" lira.toSmtLib
  assertEq "NIA"  nia.toSmtLib
  assertEq "NRA"  nra.toSmtLib
  assertEq "NIRA" nira.toSmtLib

  assertEq "QF_LIA"  qf_lia.toSmtLib
  assertEq "QF_LRA"  qf_lra.toSmtLib
  assertEq "QF_LIRA" qf_lira.toSmtLib
  assertEq "QF_NIA"  qf_nia.toSmtLib
  assertEq "QF_NRA"  qf_nra.toSmtLib
  assertEq "QF_NIRA" qf_nira.toSmtLib

  assertEq "QF_ALIA"  qf_lia.array.toSmtLib
  assertEq "QF_ANIRA" qf_nira.array.toSmtLib

  assertEq "QF_UFLIA"  qf_lia.uf.toSmtLib
  assertEq "QF_UFNIRA" qf_nira.uf.toSmtLib

  assertEq "QF_AUFLIA"  qf_lia.uf.array.toSmtLib
  assertEq "QF_AUFNIRA" qf_nira.uf.array.toSmtLib

  assertEq "QF_AUFLIA"  qf_lia.array.uf.toSmtLib
  assertEq "QF_AUFNIRA" qf_nira.array.uf.toSmtLib

  assertEq "QF_AFPLIA"  qf_lia.array.float.toSmtLib
  assertEq "QF_AFPNIRA" qf_nira.array.float.toSmtLib

  assertEq "QF_UFFPLIA"  qf_lia.uf.float.toSmtLib
  assertEq "QF_UFFPNIRA" qf_nira.uf.float.toSmtLib

  assertEq "QF_UFFFLIA"  qf_lia.uf.ff.toSmtLib
  assertEq "QF_UFFFNIRA" qf_nira.uf.ff.toSmtLib

  assertEq "QF_UFFFFPLIA"  qf_lia.uf.ff.float.toSmtLib
  assertEq "QF_UFFFFPNIRA" qf_nira.uf.ff.float.toSmtLib

  assertEq "IDL" idl.toSmtLib
  assertEq "RDL" rdl.toSmtLib

  assertEq "LIRAT" lirat.toSmtLib
  assertEq "NIAT" niat.toSmtLib

  assertEq "QF_AIDL" idl.qf.array.toSmtLib
  assertEq "QF_ARDL" rdl.qf.array.toSmtLib

  assertEq "QF_ALIRAT" lirat.qf.array.toSmtLib
  assertEq "QF_ANIAT" niat.qf.array.toSmtLib
