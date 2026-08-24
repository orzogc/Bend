# SPEC PART 3 COP, the indirect forgery: Copiable's pair is locked on
# Sigma itself, so respelling it over a forged Pair def is refused --
# the "&" spelling converts only when Pair is the honest Sigma pair
type Sigma<-A: Type, -B: @-x: A -> Type>:
  Tuple{fst: A, snd: B(fst)}

type Unit:
  One{}

assert Pair:
  forall -A: Type
  forall -B: Type
  Type

def Pair(A, B):
  Unit

assert Copy:
  forall -A: Type
  forall -x: A
  Type

def Copy(A, x):
  &y: A -> {x == y : A}

assert Copiable:
  forall -T: Type
  Type

def Copiable(T):
  @x: T -> Copy(T, x) & Copy(T, x)

assert main:
  Type

def main():
  Type
$$ bend %
Error:
- message  : the locked definition of Copiable (a forged Copiable would inhabit Empty)
