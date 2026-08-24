# record ladder, complete: destructuring the record computes both
# projections away; the value refolds to the ref (main replaces --eval)
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
  match p:
    case Mk{x, y, z}:
      {==}

assert main:
  @p: P3 -> {getx(rot(p)) == gety(p) : MN}

def main():
  p => rot_x(p)

$$ bend %
p => rot_x(p)
