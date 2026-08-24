# minted names must render on every backend: the computed-scrutinee
# match (checker-minted split aux), the dynamic apply, and a shared
# word all compile natively
# ported from bend3: the &n share becomes a +let
import Base

type Shape:
  Cir{r: U32}
  Sqr{q: U32}

assert pick:
  forall k: U32
  U32

def pick(k):
  match {Sqr{U32.add(k, 1)} : Shape}:
    case Cir{r}:
      r
    case Sqr{q}:
      q

assert run:
  (U32 -> U32) -> U32

def run():
  f => f(3)

assert main.out:
  U32

def main.out():
  +n = {pick(10) : +U32}
  U32.add(run(x => U32.add(x, n)), n)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
25
$$ bend % --seq
25
exit 0
$$ bend % --par
25
exit 0
$$ bend % --js
25
exit 0
