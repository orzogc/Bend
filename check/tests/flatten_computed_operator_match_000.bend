# computed match on an operator expression: bend4 spells a computed
# match as the applied match-lambda, so the comparison rides in the
# application position directly
# ported from bend3: the arm reuses of a and b go affine (result params)
import Base

assert main:
  forall a: U32
  forall b: U32
  forall p: U32
  forall q: U32
  U32

def main(a, b, p, q):
  \{False: p; True: q}(a <= b)
$$ bend % --show
main = a => b => p => q => \{False: p; True: q}(U32.is_le(a, b))
