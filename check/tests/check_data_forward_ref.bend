#[halts]
# bend3's sort tables were check-order-free (one global fixpoint), so
# A's field mentioned B before B's declaration under --no-halt. bend4
# has no --no-halt: the forward door is the #[halts] pragma, and under
# it the same forward chain checks and an A shares nothing (single
# uses throughout), so the program just runs.
# ported from bend3: the nested ctor pattern MkA3{MkB3{k}, n} carries;
# the let-then-call main folds to a direct sum
import Base

type A3:
  MkA3{b: B3, n: U32}
type B3:
  MkB3{k: U32}

assert get:
  forall a: A3
  U32

def get(a):
  match a:
    case MkA3{MkB3{k}, n}:
      k + n

assert main.out:
  U32

def main.out():
  get({MkA3{MkB3{40}, 2} : A3}) + get(MkA3{MkB3{0}, 0})

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
42
$$ bend % --seq
42
exit 0
$$ bend % --par
42
exit 0
$$ bend % --js
42
exit 0
