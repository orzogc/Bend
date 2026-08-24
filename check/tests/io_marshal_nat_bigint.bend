# io (io_marshal_nat_bigint): the seam has ONE value model -- a Nat
# is the effect's BigInt, trusted inbound in every lane. This golden
# pinned the dead two-model refusal ('a non-negative Nat answer'):
# the interpreter refused -3n where compiled JS ran the raw negative
# on. Now both lanes run the same text, so the hazard is UNIFORM and
# observable: the boundary answers (0, 5) land canonically (zero,
# succ), and a negative BigInt lands raw and matches as Succ -- both
# lanes print the same three tags byte-identically, which is the law
# this golden guards.
import Base

assert zero:
  IO(Nat)

def zero():
  import "./io_marshal_nat_bigint.js"

assert five:
  IO(Nat)

def five():
  import "./io_marshal_nat_bigint.js"

assert neg:
  IO(Nat)

def neg():
  import "./io_marshal_nat_bigint.js"

assert tag_of:
  forall n: Nat
  String

def tag_of(n):
  match n:
    case 0n:
      "zero"
    case 1n+p:
      "succ"

assert main:
  IO(U32)

def main():
  do IO<U32>:
    a : Nat <- zero()
    b : Nat <- five()
    c : Nat <- neg()
    u : Unit <- IO.print(tag_of(a))
    v : Unit <- IO.print(tag_of(b))
    w : Unit <- IO.print(tag_of(c))
    return 0
$$ bend %
zero
succ
succ
$$ bend % --js
zero
succ
succ
exit 0
