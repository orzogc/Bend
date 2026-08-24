# nested patterns do not widen coverage: two Sx7 rows still owe the
# Zx7 case.
# ported from bend3
type Nx7:
  Zx7{}
  Sx7{p: Nx7}

type Rx7:
  Ax7{x: Nx7}
  Bx7{x: Nx7}

assert f:
  forall a: Nx7
  Rx7

def f(a):
  match a:
    case Sx7{Sx7{a}}:
      Ax7{a}
    case Sx7{a}:
      Bx7{a}

assert main:
  Rx7

def main(): f(Sx7{Zx7{}})
$$ bend %
Error:
- expected : cases for Zx7
- observed : \{}
Location: f
16 | def f(a):
17>|   match a:
18 |     case Sx7{Sx7{a}}:
