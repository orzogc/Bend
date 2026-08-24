# audit: reserved words are rejected as pattern binders.
# ported from bend3
type Nn10:
  Zx{}
  Sx{p: Nn10}

assert f:
  forall n: Nn10
  Nn10

def f(n):
  match n:
    case Sx{return}:
      Zx{}
    case Zx{}:
      Zx{}

assert main:
  Nn10

def main(): f(Zx{})
$$ bend %
Error:
- expected : a do-block heading this return
- observed : '}'
Location:
12 |   match n:
13>|     case Sx{return}:
14 |       Zx{}
