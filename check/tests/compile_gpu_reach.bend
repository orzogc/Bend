# bend3 pinned the embedded GPU program's reachability by csrc marks;
# bend4's emitter has its own shapes, so the half that carries is the
# mark's semantics: a host-computed argument feeds a marked root and
# the value is the plain call's, on every lane (the countdown rides
# Nat: no numeric patterns)
import Base

assert cpu_only:
  forall x: Nat
  Nat

def cpu_only(x):
  Nat.mul(x, 2n)

assert gpu_only:
  forall x: Nat
  Nat

def gpu_only(x):
  match x:
    case Zero{}:
      7n
    case Succ{p}:
      Succ{gpu_only(p)}

assert main.out:
  Nat

def main.out():
  x = cpu_only(4n)
  gpu_only!(x)

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
15n
$$ bend % --seq
15n
exit 0
$$ bend % --par
15n
exit 0
$$ bend % --js
15n
exit 0
