# a let-bound redex that reduces to a lambda cannot be used twice: k
# binds Lone, and no live binding contracts.
# ported from bend3: the annotation wears the brace Ann form
import Base

type Pr12<Elem: Type>:
  P12{x: Elem, y: Elem}

assert main:
  Pr12<U32 -> U32>

def main():
  k = {(d => x => x) : Unit -> U32 -> U32}(Unit{})
  P12{k, k}
$$ bend %
Error:
- expected : k
- observed : k (consumed more than once)
Location: main
12 | def main():
13>|   k = {(d => x => x) : Unit -> U32 -> U32}(Unit{})
14 |   P12{k, k}
