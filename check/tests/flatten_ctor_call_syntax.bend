# a constructor builds with braces: A(x) is a plain call head, and no
# def A exists.
# ported from bend3
type Nw4:
  Zw4{}

type Rw4:
  Aw4{x: Nw4}

assert f:
  forall x: Nw4
  Rw4

def f(x):
  Aw4(x)

assert main:
  Rw4

def main(): f(Zw4{})
$$ bend %
Error:
- expected : a defined name
- observed : Aw4
Context:
- x : Nw4
Location: f
14 | def f(x):
15>|   Aw4(x)
16 |
