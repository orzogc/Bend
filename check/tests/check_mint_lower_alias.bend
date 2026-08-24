# bend3's mint-lowering alias witness (a split mint re-basing c^4 over
# c^3); bend4 mints nothing and stores elaborated bodies once, so the
# colliding-name shape has no machinery to alias: a field binder
# shadowing its own param beside a forall of the same name checks and
# the conversion closes
import Base

assert shadow_ok:
  forall n: Nat
  forall c: Nat
  Nat

def shadow_ok(n, c):
  match n:
    case Zero{}:
      c
    case Succ{c}:
      c

assert lem:
  forall n: Nat
  @c:Nat -> {shadow_ok(1n+n, c) == n : Nat}

def lem(n):
  c => {==}

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
