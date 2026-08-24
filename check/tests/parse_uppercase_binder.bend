# uppercase binders: lambda binders may be uppercase (Y => ...), and a
# type-parameter style bind (-A: Type) binds like any var.
# ported from bend3
type Vq2:
  Qv2{}

assert id2:
  forall -A: Type
  forall x: A
  A

def id2(A, x):
  x

assert bump:
  forall f: Vq2 -> Vq2
  forall x: Vq2
  Vq2

def bump(f, x):
  f(x)

assert main:
  Vq2

def main():
  bump(Y => Y, id2(Vq2, Qv2{}))
$$ bend %
Qv2{}
