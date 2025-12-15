
// define a procedure type
procedure intTransformer(x: int) returns (r: int)
  ensures r > x

// define a variable and assign a newly created procedure to it
var anIntTransformer: intTransformer := procedure { x + 1 };

// we can also define a procedure type, procedure value and variable assignment all at once:
procedure applyTwice(x: int, p: intTransformer) returns (r: int) {
  p(p(x))
}

// returnAdder is transparant, so the body of the created procedure is visible to the caller.
procedure returnAdder(a: int) returns (r: intTransformer) {
  var b := a;
  var r := procedure { x + b }
  b := 10;
  assert r(1) == 1 + a; // value of 'b' when procedure was created is used.
}

procedure main() {
  var c := 1;
  val p := returnAdder(c);
  c := 3;
  var d := applyTwice(2, p);
  assert d == 4; // 2 + 1 + 1, we can use the body of returnAdder to prove this
}

/*
Translation towards SMT

type ProcedureHandleIntInt
function applyIntInt(handle: ProcedureHandleIntInt, x: int): int

function line17Closure(a: int): ProcedureHandleIntInt
axiom forall a, x: int, handle: ProcedureHandleIntInt trigger applyIntInt(line17Closure(a), x) :: 
  applyIntInt(line17Closure(a), x) == x + a

function returnAdder(a: int): ProcedureHandleIntInt {
  line26Closure(a)
}
*/