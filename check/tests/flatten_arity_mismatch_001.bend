# a case narrower than its match is rejected at parse time too.
# ported from bend3
type Nw2:
  Zw2{}
  Sw2{p: Nw2}

type Rw2:
  Aw2{}

assert f:
  forall a: Nw2
  forall b: Nw2
  Rw2

def f(a, b):
  match a, b:
    case Zw2{}:
      Aw2{}

assert main:
  Rw2

def main(): f(Zw2{}, Zw2{})
$$ bend %
Error:
- expected : 2 patterns (one per scrutinee)
- observed : '
'
Location:
16 |   match a, b:
17>|     case Zw2{}:
18 |       Aw2{}
