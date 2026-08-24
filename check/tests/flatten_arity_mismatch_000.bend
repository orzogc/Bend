# a case gives ONE pattern per scrutinee, and a wider case is rejected
# at parse time.
# ported from bend3
type Nw:
  Zw{}
  Sw{p: Nw}

type Rw:
  Aw{x: Nw}
  Bw{y: Nw, z: Nw}

assert f:
  forall a: Nw
  forall b: Nw
  Rw

def f(a, b):
  match a, b:
    case Zw{}, x, Zw{}:
      Aw{x}
    case y, z:
      Bw{y, z}

assert main:
  Rw

def main(): f(Zw{}, Zw{})
$$ bend %
Error:
- expected : 2 patterns (one per scrutinee)
- observed : '
'
Location:
18 |   match a, b:
19>|     case Zw{}, x, Zw{}:
20 |       Aw{x}
