# a match missing a constructor's case is refused with the missing tag.
# ported from bend3
type Nx6:
  Zx6{}
  Sx6{p: Nx6}

type Rx6:
  Ax6{x: Nx6}

assert f:
  forall a: Nx6
  Rx6

def f(a):
  match a:
    case Sx6{a}:
      Ax6{a}

assert main:
  Rx6

def main(): f(Sx6{Zx6{}})
$$ bend %
Error:
- expected : cases for Zx6
- observed : \{}
Location: f
14 | def f(a):
15>|   match a:
16 |     case Sx6{a}:
