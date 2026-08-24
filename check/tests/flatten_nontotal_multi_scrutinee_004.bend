# red-team pin: NotTotal on a multi-scrutinee match with DISTINCT types
# names the inner column's type (elimination is column-major, left
# first): under x=Oy only Triy's Ay is covered.
# ported from bend3
type Bity:
  Oy{}
  Iy{}

type Triy:
  Ay{}
  By{}
  Cy{}

assert f:
  forall x: Bity
  forall y: Triy
  Bity

def f(x, y):
  match x, y:
    case Oy{}, Ay{}:
      Oy{}
    case Iy{}, By{}:
      Iy{}

assert main:
  Bity

def main(): f(Oy{}, Ay{})
$$ bend %
Error:
- expected : cases for By, Cy
- observed : \{}
Location: f
19 | def f(x, y):
20>|   match x, y:
21 |     case Oy{}, Ay{}:
