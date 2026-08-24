# SPEC PART 3 COP: a foreign fill dodges neither lock -- a locked name
# (Sigma, Copy, Copiable) may never be a foreign fill, and a foreign
# def must answer base's IO, not a raw name spelled IO -- so a forged
# Copiable cannot ride an import line and duplicate an affine value
assert IO:
  forall A: Type
  Type
def IO(A):
  A

assert Copiable:
  forall -T: Type
  IO(Type)
def Copiable(T):
  import "./noop.js"

assert magic:
  forall -T: Type
  IO(Copiable(T))
def magic(T):
  import "./noop.js"

type Two<-A: Type>:
  MkTwo{fst: A, snd: A}

assert dup:
  forall -A: Type
  @x: A -> Two<A>
def dup(A, x):
  +y = {x : +A ~ magic(A)};
  MkTwo{y, y}
$$ bend %
Error:
- expected : a foreign definition answering base's IO
- observed : Copiable
