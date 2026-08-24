# the wrap wall, respelled: 1 + x in an EXPRESSION is U32.add, never a
# successor witness -- f(1 + 4294967295) wraps to f(0) = 7 at runtime,
# so the free-x equation must stay stuck and {==} must refuse. bend4
# spells the arms as a literal-chain pattern and a catch-all; no Inc
# exists anywhere to close the add
import Base

assert f:
  forall n: U32
  U32

def f(n):
  match n:
    case 0:
      7
    case p:
      0

assert bad:
  forall x: U32
  {f(1 + x) == 0 : U32}

def bad(x):
  {==}

assert main:
  U32

def main():
  0
$$ bend %
Error:
- expected : f(U32.add(U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, x))
- observed : U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
Context:
- x : U32
Location: bad
23 | def bad(x):
24>|   {==}
25 |
