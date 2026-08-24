# soundness pin: a DEFAULT arm cannot smuggle one refl past a
# dependent family -- the goal stays stuck at the scrutinee (Pq(b)),
# and {==} does not check against it.
# ported from bend3
import Base

type Bq:
  Tq{}
  Fq{}

assert Pq:
  forall b: Bq
  Type

def Pq(b):
  match b:
    case Tq{}:
      {0 == 0 : U32}
    case Fq{}:
      {0 == 1 : U32}

assert ev:
  forall b: Bq
  Pq(b)

def ev(b):
  match b:
    case c:
      {==}

assert main:
  U32

def main(): 0
$$ bend %
Error:
- expected : Pq(b)
- observed : {==}
Context:
- b : Bq
Location: ev
28 |     case c:
29>|       {==}
30 |
