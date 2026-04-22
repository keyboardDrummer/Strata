/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

/-! # Multiple Output Functions

Tests that functions with multiple output parameters are correctly handled
by the EliminateMultipleOutputs pass, which synthesizes a result datatype
and rewrites call sites.
-/

def multiOutputProgram := r"
function twoOutputs(x: int)
  returns (a: int, b: int);

procedure testMultiOut() {
  var a: int;
  a := twoOutputs(5)
//     ^^^^^^^^^^^^^ error: call to 'twoOutputs' has 1 assignment target(s), but the function returns 2 output(s)
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "MultiOutput" multiOutputProgram 14 processLaurelFile

end Strata.Laurel
