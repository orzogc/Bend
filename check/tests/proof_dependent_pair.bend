# a dependent pair: the second field's type depends on the first field;
# matching refines snd's type to p(fst)
# ported from bend3: the parameterized type takes <> params like base Sigma
type N:
  Z{}
  S{p: N}
type Uni:
  U{}
type Emp:

assert isZ:
  forall n: N
  Type

def isZ(n):
  match n:
    case Z{}:
      Uni
    case S{k}:
      Emp

type DPair<-T: Type, -p: @x: T -> Type>:
  MkP{fst: T, snd: p(fst)}

assert packed:
  DPair<N, isZ>

def packed(): MkP{Z{}, U{}}

assert fst:
  forall d: DPair<N, isZ>
  N

def fst(d):
  match d:
    case MkP{a, b}:
      a

assert main:
  N

def main(): fst(packed())

$$ bend %
Z{}
