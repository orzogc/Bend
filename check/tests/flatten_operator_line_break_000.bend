# an operator never heads a continuation line: a multi-line expression
# breaks AFTER the operator
# ported from bend3: doubled operands and word literals become params
# (bend4's core is affine; a U32 literal shows as its Word chain)
import Base

assert f:
  forall a: U32
  forall b: U32
  forall c: U32
  U32

def f(a, b, c):
  x = a + b
  s = x
  s + c

assert main:
  forall a: U32
  forall b: U32
  forall c: U32
  forall d: U32
  U32

def main(a, b, c, d):
  x = (a +
    b) +
    c
  s = x
  s * d
$$ bend % --show
f = a => b => c => x = U32.add(a, b); s = x; U32.add(s, c)
main = a => b => c => d => x = U32.add(U32.add(a, b), c); s = x; U32.mul(s, d)
