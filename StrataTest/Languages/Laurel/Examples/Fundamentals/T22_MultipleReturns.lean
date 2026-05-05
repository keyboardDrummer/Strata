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
procedure multipleReturns() returns (x: int, y: int, z: int)
  opaque
  ensures x == 1 && y == 2 && z == 3;

procedure caller()
  opaque
{
  var y: int;
  assign var x: int, y, var z: int := multipleReturns();
  assert x == 1;
//^^^^^^^^^^^^^ error: assertion could not be proved
  assert y == 2;
//^^^^^^^^^^^^^ error: assertion could not be proved
  assert z == 3;
//^^^^^^^^^^^^^ error: assertion could not be proved

  var a: int;
  assign a, var b: int, var c: int := multipleReturns();
  assert a == 1;
//^^^^^^^^^^^^^ error: assertion could not be proved
  assert b == 2;
//^^^^^^^^^^^^^ error: assertion could not be proved
  assert c == 3;
//^^^^^^^^^^^^^ error: assertion could not be proved

  var m: int := 3;
  var n: int;
  n := 4
};

procedure repeatedAssignTarget()
  opaque
{
  var x: int;
  assign x, x, x := multipleReturns();
  assert x == 3
//^^^^^^^^^^^^^ error: assertion could not be proved
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "MultipleReturns" program 14 processLaurelFile

end Strata.Laurel
