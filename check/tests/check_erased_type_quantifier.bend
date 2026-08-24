# an assert may quantify over Type with an ERASED for-all (-A); the
# unannotated fill binds it erased, the instantiation still applies the
# type argument explicitly.
# ported from bend3
import Base

assert idT:
  forall -A : Type
  forall x : A
  A

def idT(A, x):
  x

assert main:
  U32

def main(): idT(U32, 9)
$$ bend %
U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
