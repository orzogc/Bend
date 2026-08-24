# an equality VALUE is affine like every live binding: one proof cannot
# feed two result slots.
# ported from bend3: bend3's Data class contracted equations freely;
# bend4 pins the refusal (core v1 has no contraction)
import Base

type Ns:
  Zs{}
  Ss{p: Ns}

assert dup_e:
  forall a: Ns
  forall b: Ns
  forall e: {a == b : Ns}
  Pair({a == b : Ns}, {a == b : Ns})

def dup_e(a, b, e):
  (e, e)

assert main:
  Ns

def main(): Zs{}
$$ bend %
Error:
- expected : e
- observed : e (consumed more than once)
Context:
- a : Ns
- b : Ns
Location: dup_e