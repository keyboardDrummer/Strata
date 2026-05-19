/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the eliminateHoles pass correctly replaces `.Hole` nodes with calls
to freshly generated uninterpreted functions, with types inferred from context.
-/

import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.InferHoleTypes
import Strata.Languages.Laurel.EliminateHoles
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator

open Strata
open Strata.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-- Parse a Laurel source string, resolve, eliminate holes, and print all procedures. -/
private def parseElimAndPrint (input : String) : IO Unit := do
  let inputCtx := Strata.Parser.stringInputContext "test" input
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let uri := Strata.Uri.file "test"
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program =>
    let result := resolve program
    let (program, model) := (result.program, result.model)
    let (program, _, _) := inferHoleTypes model program
    let (program, _) := eliminateHoles program
    for proc in program.staticProcedures do
      IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-! ## Basic: single hole in various positions -/

-- Hole in Add arg inside typed local variable → int.
/--
info: function $hole_0()
  returns ($result: int)
  opaque;
procedure test()
  opaque
{
  var x: int := 1 + $hole_0()
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
<<<<<<< HEAD
procedure test()
  opaque
{ var x: int := 1 + <?> };
=======
procedure test() opaque { var x: int := 1 + <?> };
>>>>>>> formatting-and-debugging-improvements
"

-- Bare Hole as Assign Declare initializer → replaced with call (no longer preserved as havoc).
/--
info: function $hole_0()
  returns ($result: int)
  opaque;
procedure test()
  opaque
{
  var x: int := $hole_0()
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
<<<<<<< HEAD
procedure test()
  opaque
{ var x: int := <?> };
=======
procedure test() opaque { var x: int := <?> };
>>>>>>> formatting-and-debugging-improvements
"

-- Hole in comparison arg inside assert → int (inferred from sibling literal).
/--
info: function $hole_0()
  returns ($result: int)
  opaque;
procedure test()
  opaque
{
  assert $hole_0() > 0
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
<<<<<<< HEAD
procedure test()
  opaque
{ assert <?> > 0 };
=======
procedure test() opaque { assert <?> > 0 };
>>>>>>> formatting-and-debugging-improvements
"

-- Hole directly as assert condition → bool.
/--
info: function $hole_0()
  returns ($result: bool)
  opaque;
procedure test()
  opaque
{
  assert $hole_0()
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
<<<<<<< HEAD
procedure test()
  opaque
{ assert <?> };
=======
procedure test() opaque { assert <?> };
>>>>>>> formatting-and-debugging-improvements
"

-- Hole directly as assume condition → bool.
/--
info: function $hole_0()
  returns ($result: bool)
  opaque;
procedure test()
  opaque
{
  assume $hole_0()
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
<<<<<<< HEAD
procedure test()
  opaque
{ assume <?> };
=======
procedure test() opaque { assume <?> };
>>>>>>> formatting-and-debugging-improvements
"

-- Hole as if-then-else condition → bool.
/--
info: function $hole_0()
  returns ($result: bool)
  opaque;
procedure test()
  opaque
{
  if $hole_0() then {
    assert true
  }
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
<<<<<<< HEAD
procedure test()
  opaque
{ if <?> then { assert true } };
=======
procedure test() opaque { if <?> then { assert true } };
>>>>>>> formatting-and-debugging-improvements
"

-- Hole in then-branch of if-then-else inside typed local variable → int.
/--
info: function $hole_0()
  returns ($result: int)
  opaque;
procedure test()
  opaque
{
  var x: int := if true then $hole_0() else 0
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
<<<<<<< HEAD
procedure test()
  opaque
{ var x: int := if true then <?> else 0 };
=======
procedure test() opaque { var x: int := if true then <?> else 0 };
>>>>>>> formatting-and-debugging-improvements
"

-- Hole as while-loop condition → bool.
/--
info: function $hole_0()
  returns ($result: bool)
  opaque;
procedure test()
  opaque
{
  while($hole_0()) {
    ⏎
  }
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
<<<<<<< HEAD
procedure test()
  opaque
{ while(<?>) {} };
=======
procedure test() opaque { while(<?>) {} };
>>>>>>> formatting-and-debugging-improvements
"

-- Hole as while-loop invariant → bool.
/--
info: function $hole_0()
  returns ($result: bool)
  opaque;
procedure test()
  opaque
{
  while(true)
    invariant $hole_0() {
    ⏎
  }
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
<<<<<<< HEAD
procedure test()
  opaque
{ while(true) invariant <?> {} };
=======
procedure test() opaque { while(true) invariant <?> {} };
>>>>>>> formatting-and-debugging-improvements
"

/-! ## Operators -/

-- Hole in And arg inside assert → bool.
/--
info: function $hole_0()
  returns ($result: bool)
  opaque;
procedure test()
  opaque
{
  assert true && $hole_0()
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
<<<<<<< HEAD
procedure test()
  opaque
{ assert true && <?> };
=======
procedure test() opaque { assert true && <?> };
>>>>>>> formatting-and-debugging-improvements
"

-- Hole in Neg inside typed local variable → int.
/--
info: function $hole_0()
  returns ($result: int)
  opaque;
procedure test()
  opaque
{
  var x: int := -$hole_0()
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
<<<<<<< HEAD
procedure test()
  opaque
{ var x: int := -<?> };
=======
procedure test() opaque { var x: int := -<?> };
>>>>>>> formatting-and-debugging-improvements
"

-- Hole in StrConcat inside typed local variable → string.
/--
info: function $hole_0()
  returns ($result: string)
  opaque;
procedure test()
<<<<<<< HEAD
=======
  opaque
>>>>>>> formatting-and-debugging-improvements
{
  var s: string := "hello" ++ $hole_0()
};
-/
#guard_msgs in
#eval! parseElimAndPrint
  "procedure test() opaque { var s: string := \"hello\" ++ <?> };"

/-! ## Multiple holes -/

-- Two holes in Add → both int, separate functions.
/--
info: function $hole_0()
  returns ($result: int)
  opaque;
function $hole_1()
  returns ($result: int)
  opaque;
procedure test()
  opaque
{
  var x: int := $hole_0() + $hole_1()
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
<<<<<<< HEAD
procedure test()
  opaque
{ var x: int := <?> + <?> };
=======
procedure test() opaque { var x: int := <?> + <?> };
>>>>>>> formatting-and-debugging-improvements
"

-- Holes across statements: Mul arg (int) then assert condition (bool).
/--
info: function $hole_0()
  returns ($result: int)
  opaque;
function $hole_1()
  returns ($result: bool)
  opaque;
procedure test()
  opaque
{
  var x: int := 2 * $hole_0();
  assert $hole_1()
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
<<<<<<< HEAD
procedure test()
  opaque
{ var x: int := 2 * <?>; assert <?> };
=======
procedure test() opaque { var x: int := 2 * <?>; assert <?> };
>>>>>>> formatting-and-debugging-improvements
"

/-! ## Combinations: holes in nested contexts -/

-- Hole in Add inside Gt inside if condition → int (inferred from sibling literal 0).
/--
info: function $hole_0()
  returns ($result: int)
  opaque;
procedure test()
  opaque
{
  if 1 + $hole_0() > 0 then {
    assert true
  }
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
<<<<<<< HEAD
procedure test()
  opaque
{ if 1 + <?> > 0 then { assert true } };
=======
procedure test() opaque { if 1 + <?> > 0 then { assert true } };
>>>>>>> formatting-and-debugging-improvements
"

-- Hole in Implies inside while invariant → bool.
/--
info: function $hole_0()
  returns ($result: bool)
  opaque;
procedure test()
  opaque
{
  var p: bool;
  while(true)
    invariant p ==> $hole_0() {
    ⏎
  }
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
<<<<<<< HEAD
procedure test()
  opaque
{ var p: bool; while(true) invariant p ==> <?> {} };
=======
procedure test() opaque { var p: bool; while(true) invariant p ==> <?> {} };
>>>>>>> formatting-and-debugging-improvements
"

-- Hole in Mul inside typed local variable with real type → real.
/--
info: function $hole_0()
  returns ($result: real)
  opaque;
procedure test()
  opaque
{
  var r: real := 3.14 * $hole_0()
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
<<<<<<< HEAD
procedure test()
  opaque
{ var r: real := 3.14 * <?> };
=======
procedure test() opaque { var r: real := 3.14 * <?> };
>>>>>>> formatting-and-debugging-improvements
"

/-! ## Call argument and return type inference -/

-- Hole in comparison with variable sibling → hole function takes the procedure's params.
/--
info: function $hole_0(n: int)
  returns ($result: int)
  opaque;
procedure test(n: int)
  opaque
{
  assert n > $hole_0(n)
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
<<<<<<< HEAD
procedure test(n: int)
  opaque
{ assert n > <?> };
=======
procedure test(n: int) opaque { assert n > <?> };
>>>>>>> formatting-and-debugging-improvements
"

/-! ## Holes in functions -/

-- Hole in function body → same treatment as procedures.
/--
info: function $hole_0(x: int)
  returns ($result: int)
  opaque;
function test(x: int): int
  opaque
{
  $hole_0(x)
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
<<<<<<< HEAD
function test(x: int): int
  opaque
{ <?> };
=======
function test(x: int): int opaque { <?> };
>>>>>>> formatting-and-debugging-improvements
"

/-! ## Nondeterministic holes (<??>) -/

-- Nondet hole in procedure → preserved after eliminateHoles (lifted by liftExpressionAssignments).
/--
info: procedure test()
  opaque
{
  assert <??>
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
<<<<<<< HEAD
procedure test()
  opaque
{ assert <??> };
=======
procedure test() opaque { assert <??> };
>>>>>>> formatting-and-debugging-improvements
"

-- Mixed: det hole eliminated, nondet hole preserved.
/--
info: function $hole_0()
  returns ($result: int)
  opaque;
procedure test()
  opaque
{
  var x: int := $hole_0();
  assert <??>
};
-/
#guard_msgs in
#eval! parseElimAndPrint r"
<<<<<<< HEAD
procedure test()
  opaque
{ var x: int := <?>; assert <??> };
=======
procedure test() opaque { var x: int := <?>; assert <??> };
>>>>>>> formatting-and-debugging-improvements
"

-- Nondet hole in function → should be rejected (not tested here since
-- the error occurs at Core translation time, which requires the full pipeline).

end Laurel
