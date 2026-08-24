# graph reachability over an adjacency-bitmask array: BFS by frontier
# masks (visited fixpoint), the unreachable island stays out
# ported from bend3: the slab becomes Array.new + swap writes (8 = 2^3
# slots), counters become Nat, shift counts ride U32.to_nat; strict --
# the read/dispatch defs folded into the counter matches, shared words
# +U32, walked Nats +Nat
import Base

assert wr:
  forall m: Array<U32>
  forall i: U32
  forall v: U32
  Array<U32>

def wr(m, i, v):
  (m2, old) = Array.swap(U32, m, i, v)
  m2

assert gather:
  forall i: Nat
  forall m: Array<U32>
  forall +frontier: +U32
  forall acc: U32
  (Array<U32> & U32)

def gather(i, m, frontier, acc):
  match i:
    case 0n:
      (m, acc)
    case 1n+p0:
      +p = {p0 : +Nat}
      +j = {U32.from_nat(p) : +U32}
      (m2, row) = Array.get(m, j)
      match U32.is_zero(U32.and(U32.shrn(U32.to_nat(j), frontier), 1)):
        case True{}:
          gather(p, m2, frontier, acc)
        case False{}:
          gather(p, m2, frontier, U32.or(acc, row))

assert bfs:
  forall fuel: Nat
  forall m: Array<U32>
  forall +visited: (+U32)
  (Array<U32> & U32)

def bfs(fuel, m, visited):
  match fuel:
    case 0n:
      (m, visited)
    case 1n+f:
      (m2, next) = gather(8n, m, visited, 0)
      +grown = {U32.or(visited, next) : +U32}
      match U32.is_eq(grown, visited):
        case False{}:
          bfs(f, m2, grown)
        case True{}:
          (m2, visited)

assert pop:
  forall i: Nat
  forall +n: +U32
  forall acc: U32
  U32

def pop(i, n, acc):
  match i:
    case 0n:
      acc
    case 1n+p:
      pop(p, U32.shr(n), U32.add(acc, U32.and(n, 1)))

assert build:
  Array<U32>

def build():
  wr(wr(wr(wr(wr(wr(Array.new(3n, 0), 0, 6), 1, 8), 2, 24), 3, 32), 5, 2), 6, 128)

assert go:
  forall m: Array<U32>
  U32

def go(m):
  (m2, reach0) = bfs(8n, m, 1)
  +reach = {reach0 : +U32}
  U32.add(U32.mul(reach, 100), pop(8n, reach, 0))

assert main.out:
  U32

def main.out():
  go(wr(build(), 7, 64))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
6306
$$ bend % --seq
6306
exit 0
$$ bend % --par
6306
exit 0
$$ bend % --js
6306
exit 0
