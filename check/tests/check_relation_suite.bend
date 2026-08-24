# bend3's base relations computed on concrete nats and U{} proved
# them; bend4's Nat.LE is the same computed family (Unit at yes, Empty
# at no), so Unit{} proves the concrete claims, the le lemmas ride,
# and != is the arrow into Empty discharged by a discriminator
import Base

assert Nat.LE:
  forall a: Nat
  forall b: Nat
  Type

def Nat.LE(a, b):
  match a b:
    case 0n y:
      Unit
    case 1n+x 0n:
      Empty
    case 1n+x 1n+y:
      Nat.LE(x, y)

assert Nat.le_refl:
  forall a: Nat
  Nat.LE(a, a)

def Nat.le_refl(a):
  match a:
    case 0n:
      Unit{}
    case 1n+x:
      Nat.le_refl(x)

assert le23:
  Nat.LE(2n, 3n)

def le23():
  Unit{}

assert le_r:
  forall a: Nat
  Nat.LE(a, a)

def le_r(a):
  Nat.le_refl(a)

assert isTwo:
  forall n: Nat
  Type

def isTwo(n):
  match n:
    case Succ{Succ{Zero{}}}:
      Unit
    case n:
      Empty

assert ne23:
  forall e: {2n == 3n : Nat}
  Empty

def ne23(e):
  %e : isTwo(_)
  Unit{}

assert main.out:
  Nat

def main.out():
  0n

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
0n
$$ bend % --seq
0n
exit 0
$$ bend % --par
0n
exit 0
$$ bend % --js
0n
exit 0
