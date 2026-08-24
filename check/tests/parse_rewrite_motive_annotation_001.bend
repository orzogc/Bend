# bend3 refused the '_' motive in constructor discrimination; bend4
# binds it, so the isZ transport CHECKS and 0n == 1n yields Empty --
# the inverted law at a dependent motive
import Base

assert isZ2:
  forall n: Nat
  Type

def isZ2(n):
  match n:
    case Zero{}:
      Unit
    case Succ{k}:
      Empty

assert neq:
  forall e: {0n == 1n : Nat}
  Empty

def neq(e):
  %e : isZ2(_)
  Unit{}

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
