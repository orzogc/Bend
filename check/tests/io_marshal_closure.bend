# io (io_marshal_closure): a function crosses the effect seam as a
# curried JS callback -- the compiled closure form is one-argument
# functions run to completion, so the effect applies it one argument
# at a time, any number of times, and a function it answers is
# applied by the program the same way. The pin drives all three
# doors: a two-argument callback the effect calls twice (123), a
# callback riding a ctor field out (42), and a function answer
# riding a ctor field in, applied by the program (107). Both lanes
# run the same compiled text and print byte-identically.
import Base

assert fold2:
  forall f: U32 -> U32 -> U32
  IO(U32)

def fold2(f):
  import "./io_marshal_closure.js"

assert pick_fn:
  forall m: Maybe<U32 -> U32>
  IO(U32)

def pick_fn(m):
  import "./io_marshal_closure.js"

assert stepper:
  IO(Maybe<U32 -> U32>)

def stepper():
  import "./io_marshal_closure.js"

assert app7:
  forall m: Maybe<U32 -> U32>
  U32

def app7(m):
  match m:
    case None{}:
      0
    case Some{g}:
      g(7)

assert main:
  IO(U32)

def main():
  do IO<U32>:
    a : U32 <- fold2(x => y => U32.add(U32.mul(x, 10), y))
    u : Unit <- IO.print(U32.show(a))
    b : U32 <- pick_fn(Some{x => U32.add(x, 2)})
    v : Unit <- IO.print(U32.show(b))
    m : Maybe<U32 -> U32> <- stepper()
    w : Unit <- IO.print(U32.show(app7(m)))
    return 0
$$ bend %
123
42
107
$$ bend % --js
123
42
107
exit 0
