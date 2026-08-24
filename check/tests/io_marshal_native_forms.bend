# io (io_marshal_native_forms): the native forms cross the effect
# seam canonically, both ways -- a Nat as a BigInt, a Bool as a
# boolean, a Cmp by its tag through the generic ctor lane. The legs
# escalate as io_marshal_char_type does: direct answers, an answer
# inside a Maybe field, a round trip through an argument -- and both
# lanes must print byte-identically, which one value model gives by
# construction.
import Base

assert five:
  IO(Nat)

def five():
  import "./io_marshal_native_forms.js"

assert zero:
  IO(Nat)

def zero():
  import "./io_marshal_native_forms.js"

assert wrap:
  IO(Maybe<Nat>)

def wrap():
  import "./io_marshal_native_forms.js"

assert dub:
  forall n: Nat
  IO(Nat)

def dub(n):
  import "./io_marshal_native_forms.js"

assert flip:
  forall b: Bool
  IO(Bool)

def flip(b):
  import "./io_marshal_native_forms.js"

assert ord:
  IO(Cmp)

def ord():
  import "./io_marshal_native_forms.js"

assert unwrap:
  forall m: Maybe<Nat>
  Nat

def unwrap(m):
  match m:
    case None{}:
      0n
    case Some{n}:
      n

assert cmp_name:
  forall c: Cmp
  String

def cmp_name(c):
  match c:
    case LT{}:
      "lt"
    case EQ{}:
      "eq"
    case GT{}:
      "gt"

assert main:
  IO(Unit)

def main():
  do IO<Unit>:
    a : Nat <- five()
    u1 : Unit <- IO.print(Nat.show(Nat.add(a, 3n)))
    z : Nat <- zero()
    u2 : Unit <- IO.print(Nat.show(z))
    m : Maybe<Nat> <- wrap()
    u3 : Unit <- IO.print(Nat.show(unwrap(m)))
    d : Nat <- dub(7n)
    u4 : Unit <- IO.print(Nat.show(d))
    b : Bool <- flip(True{})
    u5 : Unit <- IO.print(if b: "yes" else: "no")
    c : Cmp <- ord()
    IO.print(cmp_name(c))
$$ bend %
8
0
9
14
no
eq
$$ bend % --js
8
0
9
14
no
eq
exit 0
