# assert as a plain fn signature: the term-less entry's type is a chain
# of alls, and the later unannotated `def add(x,y):` fills it.
# ported from bend3: + becomes U32.add
import Base

assert add:
  forall x : U32
  forall y : U32
  U32

def add(x, y):
  U32.add(x, y)

assert main:
  U32

def main():
  add(40, 2)
$$ bend %
U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
