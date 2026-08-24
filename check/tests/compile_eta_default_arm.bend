# eta default: the lambda-match default tail is a bare Ref taking the
# whole value
# ported from bend3: the U32 switch becomes a lambda-match on a local
# Nat-like type; dec drops one Sc and counts the rest
import Base

type Nt:
  Zr{}
  Sc{p: Nt}

assert size:
  forall n: Nt
  U32

def size(n):
  match n:
    case Zr{}:
      0
    case Sc{p}:
      U32.add(1, size(p))

assert dec:
  forall n: Nt
  U32

def dec(n):
  match n:
    case Zr{}:
      0
    case Sc{p}:
      size(p)

assert f:
  Nt -> U32

def f():
  \{Zr: 100; dec}

assert main.out:
  U32

def main.out():
  U32.add(f(Zr{}), f(Sc{Sc{Sc{Sc{Sc{Sc{Sc{Sc{Zr{}}}}}}}}}))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
107
$$ bend % --seq
107
exit 0
$$ bend % --par
107
exit 0
$$ bend % --js
107
exit 0
