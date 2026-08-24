#[halts]
import Base
# queens: parallel exhaustive N-queens backtracking search, ported
# 1-to-1 from Bend3's par_queens. Rows 0-3 are placed up front: batch forks the flat
# (c0,c1,c2,c3) prefix index space 0..2^d as a balanced tree; each leaf
# permutes its index by an odd multiplier, decodes its column quad
# (base-N digits), keeps it when legal under the solver's own bitmask
# rules, and runs the classic recursive bitmask backtracker over the
# remaining N-4 rows: peel the lowest candidate bit b = cand & (0 -
# cand), descend on the child row's candidate word full & ~(nc|nl|nr),
# then continue on the sibling set cand - b; Stats{sols, nodes} counts
# one node per peel. smerge adds Stats pairwise up the fork tree.
# Bend3 hard-codes the prefix mask 131071 (d = 17); here the mask is
# 2^d - 1, threaded through batch, so small sizes shrink the prefix
# space the same way. solve.go/pfx.d are continuation defs: a Bend4
# match cannot follow a +local, so each peel/decode stage passes its
# shared words as + arguments. Checksum = (sols * 2654435761) ^ nodes.
# Needs #[halts]: the solver recurses on the shrinking candidate word,
# which is not structural.
#
# Sizes (d, n, limit): small (10, 5, 625) expect 774553824, big
# (17, 17, 11730) expect 2063750025. Small verified against a Bend3 C
# run on the cluster (mask 1023, run!(10, 5, 625)); big from the Bend3
# header.

type Stats:
  Stats{sols: U32, nodes: U32}

assert b2u:
  forall b: Bool
  U32

def b2u(b):
  match b:
    case False{}:
      0
    case True{}:
      1

assert sel:
  forall t: U32
  forall x: U32
  forall y: U32
  U32

def sel(t, x, y):
  match U32.is_zero(t):
    case True{}:
      x
    case False{}:
      y

assert sq:
  forall +x: U32
  U32

def sq(x):
  U32.mul(x, x)

# the classic bitmask backtracker: descend on the child candidate
# word (the natural non-tail call), then tail-loop on the sibling set
assert solve:
  forall +cand: U32
  forall +cols: U32
  forall +ld: U32
  forall +rd: U32
  forall +full: U32
  forall sols: U32
  forall nodes: U32
  Stats

def solve(cand, cols, ld, rd, full, sols, nodes):
  match U32.is_zero(cand):
    case True{}:
      Stats{sols, nodes}
    case False{}:
      +b = U32.and(cand, U32.sub(0, cand))
      solve.go(b, U32.or(cols, b), cand, cols, ld, rd, full, sols, nodes)

assert solve.go:
  forall +b: U32
  forall +nc: U32
  forall +cand: U32
  forall +cols: U32
  forall +ld: U32
  forall +rd: U32
  forall +full: U32
  forall sols: U32
  forall nodes: U32
  Stats

def solve.go(b, nc, cand, cols, ld, rd, full, sols, nodes):
  match U32.is_eq(nc, full):
    case True{}:
      solve(U32.sub(cand, b), cols, ld, rd, full, U32.inc(sols), U32.inc(nodes))
    case False{}:
      Both{nl0, nr0} = {Both{U32.shl(U32.or(ld, b)), U32.shr(U32.or(rd, b))} : Par<U32, U32>}
      +nl = nl0
      +nr = nr0
      match solve(U32.and(full, U32.not(U32.or(nc, U32.or(nl, nr)))), nc, nl, nr, full, sols, U32.inc(nodes)):
        case Stats{s1, n1}:
          solve(U32.sub(cand, b), cols, ld, rd, full, s1, n1)

# one 4-row prefix: permute the fork index (odd-multiplier bijection on
# the 2^d space), decode the column quad, filter illegal placements,
# solve the remaining rows
assert pfx:
  forall j: U32
  forall +m: U32
  forall nn: U32
  forall full: U32
  forall bound: U32
  Stats

def pfx(j, m, nn, full, bound):
  pfx.go(U32.and(U32.mul(j, 2654435761), m), nn, full, bound)

assert pfx.go:
  forall +i: U32
  forall +nn: U32
  forall full: U32
  forall bound: U32
  Stats

def pfx.go(i, nn, full, bound):
  match U32.is_lt(i, bound):
    case False{}:
      Stats{0, 0}
    case True{}:
      pfx.d(U32.mul(nn, nn), i, nn, full)

assert pfx.d:
  forall +nn2: U32
  forall +i: U32
  forall +nn: U32
  forall +full: U32
  Stats

def pfx.d(nn2, i, nn, full):
  Both{b00, b10} = {Both{U32.shln(U32.to_nat(U32.div(i, U32.mul(nn2, nn))), 1), U32.shln(U32.to_nat(U32.mod(U32.div(i, nn2), nn)), 1)} : Par<U32, U32>}
  +b0 = b00
  +b1 = b10
  match U32.is_eq(U32.and(b1, U32.or(b0, U32.or(U32.shl(b0), U32.shr(b0)))), 0):
    case False{}:
      Stats{0, 0}
    case True{}:
      Both{b20, c20} = {Both{U32.shln(U32.to_nat(U32.mod(U32.div(i, nn), nn)), 1), U32.or(b0, b1)} : Par<U32, U32>}
      +b2 = b20
      +c2 = c20
      Both{l20, r20} = {Both{U32.shl(U32.or(U32.shl(b0), b1)), U32.shr(U32.or(U32.shr(b0), b1))} : Par<U32, U32>}
      +l2 = l20
      +r2 = r20
      match U32.is_eq(U32.and(b2, U32.or(c2, U32.or(l2, r2))), 0):
        case False{}:
          Stats{0, 0}
        case True{}:
          Both{b30, c30} = {Both{U32.shln(U32.to_nat(U32.mod(i, nn)), 1), U32.or(c2, b2)} : Par<U32, U32>}
          +b3 = b30
          +c3 = c30
          Both{l30, r30} = {Both{U32.shl(U32.or(l2, b2)), U32.shr(U32.or(r2, b2))} : Par<U32, U32>}
          +l3 = l30
          +r3 = r30
          match U32.is_eq(U32.and(b3, U32.or(c3, U32.or(l3, r3))), 0):
            case False{}:
              Stats{0, 0}
            case True{}:
              Both{c40, Both{l40, r40}} = {Both{U32.or(c3, b3), Both{U32.shl(U32.or(l3, b3)), U32.shr(U32.or(r3, b3))}} : Par<U32, Par<U32, U32>>}
              +c4 = c40
              +l4 = l40
              +r4 = r40
              solve(U32.and(full, U32.not(U32.or(c4, U32.or(l4, r4)))), c4, l4, r4, full, 0, 0)

assert smerge:
  forall a: Stats
  forall b: Stats
  Stats

def smerge(a, b):
  match a b:
    case Stats{s1, n1} Stats{s2, n2}:
      Stats{U32.add(s1, s2), U32.add(n1, n2)}

assert batch:
  forall +d: Nat
  forall +i: U32
  forall +m: U32
  forall +nn: U32
  forall +full: U32
  forall +bound: U32
  Stats

def batch(d, i, m, nn, full, bound):
  match d:
    case 0n:
      pfx(i, m, nn, full, bound)
    case 1n+p:
      Both{a, b} = {Both{batch(p, i, m, nn, full, bound), batch(p, U32.add(i, U32.shln(p, 1)), m, nn, full, bound)} : Par<Stats, Stats>}
      smerge(a, b)

assert run:
  forall +d: Nat
  forall +n: U32
  forall +lim: U32
  U32

def run(d, n, lim):
  Both{nnnn0, full} = {Both{sq(sq(n)), U32.sub(U32.shln(U32.to_nat(n), 1), 1)} : Par<U32, U32>}
  +nnnn = nnnn0
  # bound = min-like clamp: lim when lim < n^4, else n^4
  match batch(d, 0, U32.sub(U32.shln(d, 1), 1), n, full, sel(b2u(U32.is_lt(lim, nnnn)), nnnn, lim)):
    case Stats{s, w}:
      U32.xor(U32.mul(s, 2654435761), w)

assert size:
  U32

def size():
  17

assert limit:
  U32

def limit():
  11730

# small: run!(10n, 5, 625) expect 774553824; big expect 2063750025
assert main:
  IO(Unit)

def main():
  IO.print(U32.show(run!(17n, size(), limit())))
