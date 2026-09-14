import Base
# editdist: Levenshtein edit distance by dynamic programming over flat
# Array<U32> rows -- the suite's arrays-of-words case. 2^K independent
# pairs fork as a balanced batch tree. Pair p hashes its index into an
# xorshift seed and draws two sequences of N = 256 symbols over a
# 4-letter alphabet (a symbol is the low two bits of the stream; the
# second stream starts at the first seed times an odd constant), each
# written slot by slot into its own 256-slot Array<U32>. The DP walks
# the N x N cell grid with two rolling 512-slot rows, prev and cur:
# prev[j] = j at the start; row i reads a[i] once, writes cur[0] =
# i + 1, then for each j in 0..N-1 reads b[j], prev[j], prev[j+1] and
# cur[j] and writes cur[j+1] = min(prev[j+1] + 1, cur[j] + 1, prev[j]
# + cost), cost 0 when a[i] == b[j] and 1 otherwise; when the row
# ends the rows swap roles. The distance is prev[N] after the last
# row. A pair's checksum mixes its distance with its index; pair
# checksums sum up the fork tree. Knob: K (2^K pairs, 2x per notch).
#
# Spelling notes: `x[i]` reads are Array.get(U32, x, i), which hands
# the array back with the word as a pair, destructured at the top of
# the next stage def (a Bend4 match cannot scrutinize a computed
# value); `x[i] <- v` writes hand the array back alone. The four live
# arrays ride together in the Dp record (a Type, so it may hold
# arrays), opened by pattern at each cell and rebuilt after its write.
# Loop counters are Nats (no U32 match in Bend4) with the U32 index
# alongside; min is a Bool match on U32.is_lt; cost is b2u of
# U32.is_ne.
#
# Sizes: small K = 2n (expect 2065873279, verified against the C
# twin), big K = 15n (expect 2229810577).

type Dp is Type:
  Dp{a: Array<U32>, b: Array<U32>, prev: Array<U32>, cur: Array<U32>}

law b2u:
  for b: Bool
  U32

def b2u(b):
  match b:
    case False{}:
      0
    case True{}:
      1

# xorshift: x ^= x<<13; x ^= x>>17; x ^= x<<5
law prng:
  for +x: U32
  U32

def prng(x):
  +b = U32.xor(x, U32.shln(x, 13n))
  +d = U32.xor(b, U32.shrn(b, 17n))
  U32.xor(d, U32.shln(d, 5n))

law umin.go:
  for x: U32
  for y: U32
  for lt: Bool
  U32

def umin.go(x, y, lt):
  match lt:
    case True{}:
      x
    case False{}:
      y

law umin:
  for +x: U32
  for +y: U32
  U32

def umin(x, y):
  umin.go(x, y, U32.is_lt(x, y))

# draw one sequence: step the stream, write its low two bits at slot k
law gen:
  for +j: Nat
  for +k: U32
  for +s: U32
  for x: Array<U32>
  Array<U32>

def gen(j, k, s, x):
  match j:
    case 0n:
      x
    case 1n+q:
      +s2 = prng(s)
      gen(q, U32.inc(k), s2, x[k] <- U32.and(s2, 3))

# prev[k] = k: the row of the empty prefix
law init:
  for +j: Nat
  for +k: U32
  for x: Array<U32>
  Array<U32>

def init(j, k, x):
  match j:
    case 0n:
      x
    case 1n+q:
      init(q, U32.inc(k), x[k] <- k)

# one DP cell at column j: 4 reads + 1 write, each read's pair riding
# into the next stage def; the last stage rebuilds the state record
law cell.f4:
  for +j: U32
  for cost: U32
  for diag: U32
  for up: U32
  for a: Array<U32>
  for b: Array<U32>
  for prev: Array<U32>
  for r: Array<U32> & U32
  Dp

def cell.f4(j, cost, diag, up, a, b, prev, r):
  (cur, left) = r
  v = umin(umin(U32.inc(up), U32.inc(left)), U32.add(diag, cost))
  Dp{a, b, prev, cur[U32.inc(j)] <- v}

law cell.f3:
  for +j: U32
  for cost: U32
  for diag: U32
  for a: Array<U32>
  for b: Array<U32>
  for cur: Array<U32>
  for r: Array<U32> & U32
  Dp

def cell.f3(j, cost, diag, a, b, cur, r):
  (prev, up) = r
  cell.f4(j, cost, diag, up, a, b, prev, Array.get(U32, cur, j))

law cell.f2:
  for +j: U32
  for cost: U32
  for a: Array<U32>
  for b: Array<U32>
  for cur: Array<U32>
  for r: Array<U32> & U32
  Dp

def cell.f2(j, cost, a, b, cur, r):
  (prev, diag) = r
  cell.f3(j, cost, diag, a, b, cur, Array.get(U32, prev, U32.inc(j)))

law cell.f1:
  for +j: U32
  for ai: U32
  for a: Array<U32>
  for prev: Array<U32>
  for cur: Array<U32>
  for r: Array<U32> & U32
  Dp

def cell.f1(j, ai, a, prev, cur, r):
  (b, bj) = r
  cell.f2(j, b2u(U32.is_ne(ai, bj)), a, b, cur, Array.get(U32, prev, j))

law cell:
  for +j: U32
  for ai: U32
  for st: Dp
  Dp

def cell(j, ai, st):
  Dp{a, b, prev, cur} = st
  cell.f1(j, ai, a, prev, cur, Array.get(U32, b, j))

# one DP row: N cells in ascending column order; when the row ends
# the rows swap roles
law row:
  for +n: Nat
  for +j: U32
  for +ai: U32
  for st: Dp
  Dp

def row(n, j, ai, st):
  match n:
    case 0n:
      Dp{a, b, prev, cur} = st
      Dp{a, b, cur, prev}
    case 1n+q:
      row(q, U32.inc(j), ai, cell(j, ai, st))

# row i's prologue: read a[i] (its pair rides into dp.f1), write
# cur[0] = i + 1, then run the row
law dp.f1:
  for +i: U32
  for b: Array<U32>
  for prev: Array<U32>
  for cur: Array<U32>
  for r: Array<U32> & U32
  Dp

def dp.f1(i, b, prev, cur, r):
  (a, ai) = r
  row(256n, 0, ai, Dp{a, b, prev, cur[0] <- U32.inc(i)})

law dp.row:
  for +i: U32
  for st: Dp
  Dp

def dp.row(i, st):
  Dp{a, b, prev, cur} = st
  dp.f1(i, b, prev, cur, Array.get(U32, a, i))

# the DP: N rows
law dp:
  for +n: Nat
  for +i: U32
  for st: Dp
  Dp

def dp(n, i, st):
  match n:
    case 0n:
      st
    case 1n+q:
      dp(q, U32.inc(i), dp.row(i, st))

# the distance: prev[N] after the last row; the rest of the state
# drops
law dist.fin:
  for r: Array<U32> & U32
  U32

def dist.fin(r):
  (prev, d) = r
  d

law dist:
  for st: Dp
  U32

def dist(st):
  Dp{a, b, prev, cur} = st
  dist.fin(Array.get(U32, prev, 256))

# one pair: seed from the hashed pair index, draw a and b, run the DP,
# mix the distance with the index
law pair:
  for +p: U32
  U32

def pair(p):
  +s = U32.mul(U32.inc(p), 2654435761)
  a = gen(256n, 0, s, [0 : U32*256n])
  b = gen(256n, 0, U32.mul(s, 340573321), [0 : U32*256n])
  prev = init(257n, 0, [0 : U32*512n])
  d = dist(dp(256n, 0, Dp{a, b, prev, [0 : U32*512n]}))
  U32.xor(U32.mul(d, 2654435761), U32.inc(p))

# batch tree over the pair index space
law batch:
  for +d: Nat
  for +p: U32
  U32

def batch(d, p):
  match d:
    case 0n:
      pair(p)
    case 1n+q:
      x y = batch(q, p) batch(q, U32.add(p, U32.shln(1, q)))
      U32.add(x, y)

law size.small:
  Nat

def size.small():
  2n

law size.big:
  Nat

def size.big():
  15n

# small: batch!(size.small(), 0) expect 2065873279; big
# batch!(size.big(), 0) expect 2229810577
law main:
  IO(Unit)

def main():
  IO.print(U32.show(batch!(size.big(), 0)))
