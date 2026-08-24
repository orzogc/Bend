# bend3's %e renormalized every ctx type at 3000 levels; bend4's
# rewrite is goal-only by ruling (ctx renormalization is on the
# do-not-add list), so the class pins on the goal: a 3000-deep
# equation rides one rewrite and closes, no host recursion anywhere
# (the countdown spells Nat: no number switches)
import Base

assert build:
  forall n: Nat
  Nat

def build(n):
  match n:
    case Zero{}:
      0n
    case Succ{k}:
      Succ{Succ{build(k)}}

assert shrink:
  forall e: {build(1500n) == 3000n : Nat}
  {Succ{build(1500n)} == 3001n : Nat}

def shrink(e):
  %e : {Succ{_} == 3001n : Nat}
  {==}

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
