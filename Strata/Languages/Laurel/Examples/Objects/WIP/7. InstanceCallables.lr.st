/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/
composite Base {
  procedure foo(): int
    reads this
    ensures result > 3
    { abstract }
}

composite Extender1 extends Base {
  procedure foo(): int
    reads this
    ensures result > 4
//  ^^^^^^^ error: could not prove ensures clause guarantees that of extended method 'Base.foo'
    { abstract }
}

composite Extender2 extends Base {
  value: int
  procedure foo(): int
    reads this
    ensures result > 2
  {
    this.value + 2 // 'this' is an implicit variable inside instance callables
  }
}

val foo = procedure(b: Base) {
  var x = b.foo();
  assert x > 3; // pass
}

/*
Translation towards SMT

type TypedRef
function extender2(ref: Ref): TypedRef
function foo(heap: Heap, ref: TypedRef): int

const Extender2: CompositeType

// Extender2.foo
axiom forall ref: Ref, heap: Heap trigger foo(heap, extender2(ref)) :: foo(heap, extender2(ref)) == getValue(r) + 2
*/