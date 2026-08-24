# bend3 refused '_' in rewrite motives ('a defined name'); bend4 binds
# '_' there by design, so the natural sym and cong spellings CHECK --
# the inverted law, pinned positively
import Base

assert sym3:
  forall -a: Type
  forall -x: a
  forall -y: a
  forall e: {x == y : a}
  {y == x : a}

def sym3(a, x, y, e):
  %e : {_ == x : a}
  {==}

assert cong3:
  forall -a: Type
  forall -b: Type
  forall -f: a -> b
  forall -u: a
  forall -v: a
  forall e: {u == v : a}
  {f(u) == f(v) : b}

def cong3(a, b, f, u, v, e):
  %e : {f(u) == f(_) : b}
  {==}

assert main.out:
  U32

def main.out():
  0

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
0
$$ bend % --seq
0
exit 0
$$ bend % --par
0
exit 0
$$ bend % --js
0
exit 0
