# error census: a statement head that is neither binder nor ctor
# pattern (f(1) = 3) fails at the reinterpret point.
# ported from bend3
import Base

assert f:
  forall x: U32
  U32

def f(x):
  x

assert main:
  U32

def main():
  f(1) = 3
  0
$$ bend %
Error:
- expected : a pattern (a binder or a constructor)
- observed : f(U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})
Location:
16 | def main():
17>|   f(1) = 3
18 |   0
