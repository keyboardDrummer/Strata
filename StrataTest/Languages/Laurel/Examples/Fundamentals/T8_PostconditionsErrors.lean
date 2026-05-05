/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

def program := r"

function opaqueFunction(x: int) returns (r: int)
//       ^^^^^^^^^^^^^^ error: functions with postconditions are not yet supported
  requires x > 0
  opaque
  ensures r > 0
{
  x
};

procedure callerOfOpaqueFunction()
  opaque
{
  var x: int := opaqueFunction(3);
  assert x > 0;
// The following assertion should fail but does not
  assert x == 3
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "Postconditions" program 14 processLaurelFile
