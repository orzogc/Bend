# a non-decreasing recursive call through a computed match is rejected:
# descent needs some live argument to shrink.
# ported from bend3
type Bx4:
  Tx4{}
  Fx4{}

assert flip:
  forall a: Bx4
  Bx4

def flip(a):
  match a:
    case Tx4{}:
      Fx4{}
    case Fx4{}:
      Tx4{}

assert bad:
  forall b: Bx4
  Bx4

def bad(b):
  match flip(b):
    case Tx4{}:
      bad(b)
    case Fx4{}:
      Fx4{}

assert main:
  Bx4

def main(): Fx4{}
$$ bend %
Error:
- expected : a decreasing self-call (some live argument must shrink)
- observed : bad(b)
Context:
- b : Bx4
Location: bad
25 |     case Tx4{}:
26>|       bad(b)
27 |     case Fx4{}:
