# an equation goal whose sides are 0-param def calls makes conversion
# run seed's ELABORATED body -- checking prf leaves the body intact
# end-to-end.
# ported from bend3: the let value wears an Ann (a bare literal cannot
# infer), and the body stays affine (x used once)
import Base

assert seed:
  U32

def seed():
  x = {3 : U32}
  U32.add(x, 39)

assert prf:
  {seed() == seed() : U32}

def prf():
  {==}

assert main:
  U32

def main():
  seed()
$$ bend %
U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
