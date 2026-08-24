# a param named after a top-level def SHADOWS it inside its body (a
# bound Var, never the Ref), while call sites outside still reach the
# def.
# ported from bend3: the shadowing body stays affine (one use)
import Base

assert f:
  forall x: U32
  U32

def f(x):
  U32.add(x, 1)

assert g:
  forall f: U32
  U32

def g(f):
  f

assert main:
  U32

def main(): g(f(3))
$$ bend %
U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
