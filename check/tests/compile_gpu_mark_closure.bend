# bend3 pinned the marked partial call's runtime closure by csrc marks
# (G_WALK aliases); bend4's emitter has its own closure shapes, so the
# semantic half carries: a marked partial named call, ascribed and
# passed as a closure, answers the plain chain's value (the countdown
# rides Nat)
import Base

assert walk:
  forall d: Nat
  forall x: U32
  U32

def walk(d, x):
  match d:
    case Zero{}:
      x
    case Succ{p}:
      walk(p, x + 1)

assert use:
  forall f: U32 -> U32
  forall x: U32
  U32

def use(f, x):
  f(x)

assert main.out:
  Nat

def main.out():
  f = {walk!(4n) : U32 -> U32}
  U32.to_nat(use(f, 3))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
7n
$$ bend % --js
7n
exit 0
