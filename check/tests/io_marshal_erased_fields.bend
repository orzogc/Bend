# io (io_marshal_erased_fields): a ctor crosses the effect seam in
# the emitter's object shape -- live fields numbered densely ($0..),
# erased fields absent. The .js body reads $0 as the VALUE, not the
# erased tag, and a ctor it answers carries live fields only; the
# interpreter runs the compiled JS, so the shape is one by
# construction. Both lanes print the same bytes: the value out (42),
# the value in (99).
import Base

type Box:
  MkBox{-tag: Nat, val: U32}

assert box_val:
  forall b: Box
  IO(U32)

def box_val(b):
  import "./io_marshal_erased_fields.js"

assert box_new:
  IO(Box)

def box_new():
  import "./io_marshal_erased_fields.js"

assert box_open:
  forall b: Box
  U32

def box_open(b):
  match b:
    case MkBox{t, v}:
      v

assert main:
  IO(U32)

def main():
  do IO<U32>:
    x : U32 <- box_val(MkBox{7n, 42})
    u : Unit <- IO.print(U32.show(x))
    b : Box <- box_new()
    w : Unit <- IO.print(U32.show(box_open(b)))
    return 0
$$ bend %
42
99
$$ bend % --js
42
99
exit 0
