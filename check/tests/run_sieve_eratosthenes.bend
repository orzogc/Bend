# sieve of Eratosthenes over a word array: mark multiples in place,
# count survivors -- 11 primes at or below 31
# ported from bend3: the 32-slot slab becomes Array.new(5n, 0), fuel
# and walk counters become Nat, U32 dispatches nested Bool matches
# (j >= 2 is spelled U32.is_le(2, j): tocl lacks u32_is_ge, see
# run_word_compare's yellow); strict -- the continuation defs folded
# into the fuel matches, shared words +U32, walked Nats +Nat
import Base

assert wr:
  forall m: Array<U32>
  forall i: U32
  forall v: U32
  Array<U32>

def wr(m, i, v):
  (m2, old) = Array.swap(U32, m, i, v)
  m2

assert mark:
  forall fuel: Nat
  forall +mult: +U32
  forall +step: +U32
  forall m: Array<U32>
  Array<U32>

def mark(fuel, mult, step, m):
  match fuel:
    case 0n:
      m
    case 1n+f:
      match U32.is_lt(mult, 32):
        case False{}:
          m
        case True{}:
          mark(f, U32.add(mult, step), step, wr(m, mult, 1))

assert sieve:
  forall fuel: Nat
  forall +p: +U32
  forall m: Array<U32>
  Array<U32>

def sieve(fuel, p, m):
  match fuel:
    case 0n:
      m
    case 1n+f:
      (m2, v) = Array.get(m, p)
      match U32.is_zero(v):
        case True{}:
          sieve(f, U32.add(p, 1), mark(16n, U32.mul(p, p), p, m2))
        case False{}:
          sieve(f, U32.add(p, 1), m2)

assert survivors:
  forall i: Nat
  forall m: Array<U32>
  forall acc: U32
  U32

def survivors(i, m, acc):
  match i:
    case 0n:
      acc
    case 1n+p0:
      +p = {p0 : +Nat}
      +j = {U32.from_nat(p) : +U32}
      (m2, v) = Array.get(m, j)
      match U32.is_le(2, j):
        case False{}:
          acc
        case True{}:
          match U32.is_zero(v):
            case True{}:
              survivors(p, m2, U32.add(acc, 1))
            case False{}:
              survivors(p, m2, acc)

assert main.out:
  U32

def main.out():
  survivors(32n, sieve(4n, 2, Array.new(5n, 0)), 0)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
11
$$ bend % --seq
11
exit 0
$$ bend % --par
11
exit 0
$$ bend % --js
11
exit 0
