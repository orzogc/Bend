# erased constructor fields: `-A: Type` in a type declaration exists
# only at check time. Construction supplies the erased argument
# explicitly; an erased def param may legally feed it. Matching binds
# the erased field too, but it must stay unused.
# ported from bend3: def <A> params become an erased -A bind
import Base

type Bxb:
  Mkb{-A: Type, v: A, tag: Nat}

assert mk:
  forall -A: Type
  forall x: A
  Bxb

def mk(A, x):
  Mkb{A, x, 7n}

assert peek:
  forall b: Bxb
  Nat

def peek(b):
  match b:
    case Mkb{A, v, tag}:
      tag

assert main:
  Nat

def main(): peek(mk(Nat, 3n))
$$ bend %
7n
