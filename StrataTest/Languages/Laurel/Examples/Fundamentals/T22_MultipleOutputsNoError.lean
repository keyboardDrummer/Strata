/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

/-! # Multiple Output Functions (No Error)

Tests that a function with multiple output parameters is accepted
by the EliminateMultipleOutputs pass when there is no mismatched call site.
-/

def multiOutputNoErrorProgram := r"
function twoOutputs(x: int)
  returns (a: int, b: int);
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "MultiOutputNoError" multiOutputNoErrorProgram 20 processLaurelFile

end Strata.Laurel
