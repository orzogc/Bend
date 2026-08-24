#[halts]
import Base
# Game of Life: Conway soup census (Catagolue-style soup search),
# ported 1-to-1 from Bend3's par_gameoflife. 64*2^size random 4x4-toroidal soups, each
# packed in one U32, fork as a balanced batch tree of 2^size 64-soup
# leaf chunks. Every soup runs gens generations of the bit-packed
# Conway step, then is classified by two probe steps -- still life
# (fixed point), period-2 oscillator, or chaos -- and popcounted by a
# 16-bit SWAR fold. A chunk accumulates population, the two class
# tallies and a board hash in scalar registers, materializing one
# Census per chunk; czip merges censuses up the fork tree and the
# checksum mixes the final census. Counters ride as Nats (no U32 match
# in Bend4); classify.p1 is a continuation def (a Bend4 match cannot
# follow a +local). This replaces the older Array-grid port, whose
# Bend3 counterpart no longer exists.
#
# Sizes (size, gens): small (1, 2) expect 2601177279 (verified against
# a Bend3 C run on the cluster), big (18, 32) expect 2016151040 (from
# the Bend3 header).

type Cls:
  Still{}
  Osc{}
  Chaos{}

type Census:
  Census{pop: U32, still: U32, osc: U32, mix: U32}

assert b2u:
  forall b: Bool
  U32

def b2u(b):
  match b:
    case False{}:
      0
    case True{}:
      1

assert cell_get:
  forall board: U32
  forall r: U32
  forall c: U32
  U32

def cell_get(board, r, c):
  U32.and(U32.shrn(U32.to_nat(U32.and(U32.add(U32.mul(U32.and(r, 3), 4), U32.and(c, 3)), 31)), board), 1)

assert neighbor_count:
  forall +board: U32
  forall +r: U32
  forall +c: U32
  U32

def neighbor_count(board, r, c):
  U32.add(cell_get(board, U32.sub(r, 1), U32.sub(c, 1)), U32.add(cell_get(board, U32.sub(r, 1), c), U32.add(cell_get(board, U32.sub(r, 1), U32.add(c, 1)), U32.add(cell_get(board, r, U32.sub(c, 1)), U32.add(cell_get(board, r, U32.add(c, 1)), U32.add(cell_get(board, U32.add(r, 1), U32.sub(c, 1)), U32.add(cell_get(board, U32.add(r, 1), c), cell_get(board, U32.add(r, 1), U32.add(c, 1)))))))))

assert next_dead:
  forall n: U32
  U32

def next_dead(n):
  b2u(U32.is_eq(n, 3))

assert next_alive:
  forall +n: U32
  U32

def next_alive(n):
  b2u(Bool.or(U32.is_eq(n, 2), U32.is_eq(n, 3)))

assert next_cell:
  forall a: U32
  forall n: U32
  U32

def next_cell(a, n):
  match U32.is_zero(a):
    case True{}:
      next_dead(n)
    case False{}:
      next_alive(n)

assert step_cell:
  forall +board: U32
  forall +pos: U32
  U32

def step_cell(board, pos):
  +rr = U32.shrn(2n, pos)
  +cc = U32.and(pos, 3)
  alive = cell_get(board, rr, cc)
  neighbors = neighbor_count(board, rr, cc)
  U32.shln(U32.to_nat(U32.and(pos, 31)), next_cell(alive, neighbors))

assert step:
  forall +b: U32
  U32

def step(b):
  U32.or(step_cell(b, 0), U32.or(step_cell(b, 1), U32.or(step_cell(b, 2), U32.or(step_cell(b, 3), U32.or(step_cell(b, 4), U32.or(step_cell(b, 5), U32.or(step_cell(b, 6), U32.or(step_cell(b, 7), U32.or(step_cell(b, 8), U32.or(step_cell(b, 9), U32.or(step_cell(b, 10), U32.or(step_cell(b, 11), U32.or(step_cell(b, 12), U32.or(step_cell(b, 13), U32.or(step_cell(b, 14), step_cell(b, 15))))))))))))))))

assert run:
  forall n: Nat
  forall board: U32
  U32

def run(n, board):
  match n:
    case 0n:
      board
    case 1n+p:
      run(p, step(board))

# 16-bit SWAR population count
assert popcount:
  forall +b: U32
  U32

def popcount(b):
  +a = U32.sub(b, U32.and(U32.shrn(1n, b), 21845))
  +c = U32.add(U32.and(a, 13107), U32.and(U32.shrn(2n, a), 13107))
  d = U32.and(U32.add(c, U32.shrn(4n, c)), 3855)
  U32.and(U32.shrn(8n, U32.mul(d, 257)), 31)

assert classify.p1:
  forall +n1: U32
  forall +b: U32
  Cls

def classify.p1(n1, b):
  match U32.is_eq(n1, b):
    case True{}:
      Still{}
    case False{}:
      match U32.is_eq(step(n1), b):
        case True{}:
          Osc{}
        case False{}:
          Chaos{}

# classify the settled board by two probe steps: fixed point = still
# life, return after two = period-2 oscillator, anything else = chaos
assert classify:
  forall +b: U32
  Cls

def classify(b):
  classify.p1(step(b), b)

# one soup: hash the soup index into a 16-bit board, run gens steps
assert sim:
  forall ix: U32
  forall g: Nat
  U32

def sim(ix, g):
  run(g, U32.and(U32.mul(ix, 2654435761), 65535))

# leaf chunk: 64 soups folded into scalar accumulators; the Census
# ctor materializes once per chunk, never per soup
assert chunk:
  forall +j: Nat
  forall +i: U32
  forall +g: Nat
  forall pa: U32
  forall sa: U32
  forall oa: U32
  forall mx: U32
  Census

def chunk(j, i, g, pa, sa, oa, mx):
  match j:
    case 0n:
      Census{pa, sa, oa, mx}
    case 1n+p:
      Both{bd0, mxk0} = {Both{sim(U32.add(i, U32.from_nat(p)), g), U32.mul(mx, 2654435761)} : Par<U32, U32>}
      +bd = bd0
      +mxk = mxk0
      match classify(bd):
        case Still{}:
          chunk(p, i, g, U32.add(pa, popcount(bd)), U32.inc(sa), oa, U32.xor(mxk, bd))
        case Osc{}:
          chunk(p, i, g, U32.add(pa, popcount(bd)), sa, U32.inc(oa), U32.xor(mxk, bd))
        case Chaos{}:
          chunk(p, i, g, U32.add(pa, popcount(bd)), sa, oa, U32.xor(mxk, bd))

assert czip:
  forall a: Census
  forall b: Census
  Census

def czip(a, b):
  match a b:
    case Census{p, s, o, m} Census{q, t, r, n}:
      Census{U32.add(p, q), U32.add(s, t), U32.add(o, r), U32.add(U32.mul(m, 2654435761), n)}

assert batch:
  forall +d: Nat
  forall +i: U32
  forall +g: Nat
  Census

def batch(d, i, g):
  match d:
    case 0n:
      chunk(64n, i, g, 0, 0, 0, 0)
    case 1n+p:
      Both{a, b} = {Both{batch(p, i, g), batch(p, U32.add(i, U32.shln(p, 64)), g)} : Par<Census, Census>}
      czip(a, b)

# final checksum: mix the census fields
assert cfin:
  forall c: Census
  U32

def cfin(c):
  match c:
    case Census{p, s, o, m}:
      U32.add(U32.mul(U32.add(U32.mul(U32.add(U32.mul(p, 2654435761), s), 2654435761), o), 2654435761), m)

assert size:
  Nat

def size():
  18n

assert gens:
  Nat

def gens():
  32n

# small: size 1n gens 2n expect 2601177279; big expect 2016151040
assert main:
  IO(Unit)

def main():
  IO.print(U32.show(cfin(batch!(size(), 0, gens()))))
