# red-team pin: a statement's RHS expression breaks AFTER an operator
# (`x = s .&.` then the next line's operand).
# ported from bend3: doubled operand and word literal become params
import Base

assert main:
  forall a: U32
  forall m: U32
  forall w: U32
  U32

def main(a, m, w):
  s = a
  x = s .&.
    m
  x + w
$$ bend % --show
main = a => m => w => s = a; x = U32.and(s, m); U32.add(x, w)
