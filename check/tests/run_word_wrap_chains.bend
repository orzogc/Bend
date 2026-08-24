# wrap-around arithmetic chains: xorshift32, a modular-inverse round trip,
# a 31x hash chain and a wrapped fibonacci loop all land on pinned words
# ported from bend3: shift counts become Nat (U32.shln/shrn), loop
# counters become Nat, shared words become +U32 Cop binders
import Base

assert bu:
  forall b: Bool
  U32

def bu(b):
  match b:
    case False{}:
      0
    case True{}:
      1

assert xorshift:
  forall +x: +U32
  U32

def xorshift(x):
  +a = {U32.xor(x, U32.shln(13n, x)) : +U32}
  +b = {U32.xor(a, U32.shrn(17n, a)) : +U32}
  U32.xor(b, U32.shln(5n, b))

assert hash_go:
  forall n: Nat
  forall +i: +U32
  forall h: U32
  U32

def hash_go(n, i, h):
  match n:
    case 0n:
      h
    case 1n+p:
      hash_go(p, U32.add(i, 1), U32.add(U32.mul(h, 31), i))

assert fib_go:
  forall n: Nat
  forall a: U32
  forall +b: +U32
  U32

def fib_go(n, a, b):
  match n:
    case 0n:
      a
    case 1n+p:
      fib_go(p, b, U32.add(a, b))

assert main.out:
  U32

def main.out():
  b0 = bu(U32.is_eq(xorshift(xorshift(xorshift(2463534242))), 2064144800))
  b1 = bu(U32.is_eq(U32.mul(U32.mul(123456789, 2654435761), 244002641), 123456789))
  b2 = bu(U32.is_eq(hash_go(5n, 1, 7), 201390172))
  b3 = bu(U32.is_eq(fib_go(24n, 4000000000, 4100000000), 280414208))
  U32.add(U32.add(U32.add(b0, b1), b2), b3)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
4
$$ bend % --seq
4
exit 0
$$ bend % --par
4
exit 0
$$ bend % --js
4
exit 0
