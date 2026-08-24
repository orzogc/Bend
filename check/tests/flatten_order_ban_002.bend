# THE ORDER BAN, locals: the head-binder window is one statement deep,
# so a constructor destructure must sit adjacent to the statement that
# binds its scrutinee -- any local between them takes the head and the
# destructure dies at the ban, like every out-of-order match.
type Nw:
  Zw{}
  Sw{p: Nw}

assert f:
  forall x: Nw
  Nw

def f(x):
  y = Sw{x}
  z = Zw{}
  Sw{p} = y
  p

assert main:
  Nw

def main():
  Zw{}
$$ bend %
Error:
- message  : match scrutinees in binder order (this variable is unbound, consumed, or out of order: reorder the match)
Location:
15 |   z = Zw{}
16>|   Sw{p} = y
17 |   p
