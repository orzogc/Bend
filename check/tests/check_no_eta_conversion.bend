# conversion is up to ETA for functions: {(x => g(x)) == g} at a
# function carrier closes by refl.
# ported from bend3: bend3 refused eta; bend4 pins the opposite law
import Base

assert f:
  forall g: U32 -> U32
  {(x => g(x)) == g : U32 -> U32}

def f(g):
  {==}

assert main:
  U32

def main(): 0
$$ bend %
U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
