# record ladder, state 0: goals holding FIELD PROJECTIONS through a
# rebuild -- getx(rot(p)) stays a ref chain on the stuck record var
type MN:
  Z{}
  S{p: MN}

type P3:
  Mk{x: MN, y: MN, z: MN}

assert rot:
  forall p: P3
  P3

def rot(p):
  match p:
    case Mk{x, y, z}:
      Mk{y, z, x}

assert getx:
  forall p: P3
  MN

def getx(p):
  match p:
    case Mk{x, y, z}:
      x

assert gety:
  forall p: P3
  MN

def gety(p):
  match p:
    case Mk{x, y, z}:
      y

assert rot_x:
  forall p: P3
  {getx(rot(p)) == gety(p) : MN}

def rot_x(p):
  {==}

$$ bend %
Error:
- expected : getx(rot(p))
- observed : gety(p)
Context:
- p : P3
Location: rot_x
41 | def rot_x(p):
42>|   {==}
43 |
