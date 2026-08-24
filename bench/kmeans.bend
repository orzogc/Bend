#[halts]
import Base
# kmeans: k-means clustering with random restarts, ported 1-to-1 from
# Bend3's par_kmeans. 64 independent restarts fork as a batch tree; each
# runs 20 Lloyd rounds over 2^SIZE prng points (10-bit 2D coords,
# regenerated from their index hash) and K = 8 clusters. A round folds
# the point tree in 64-point leaf chunks: a chunk picks each point's
# nearest centroid (8 squared distances, branchless argmin) and
# accumulates 8x{sx,sy,n} in 24 scalar registers -- pure uniform
# arithmetic -- materializing one complete stats tree per chunk; szip
# merges the trees pairwise up the forked reduction, and the round
# extracts the 8 new centroids (sum/count, empty keeps the old one).
# Checksum sums the restarts' final-centroid mixes. Round, chunk and
# depth counters are Nats (no U32 match in Bend4).
#
# NO TUNING: this file is the elegant spelling BY LAW (bench.ts
# header). A flat-24-scalar-record rewrite of the stats merge
# (cca3d150) measured GPU 0.65 -> 0.17s and was REVERTED on Taelin's
# order 2026-07-24: it tuned the bench, not the compiler. The gap is
# the seq-machine frame class on the boxed merge (RULES.md (runtime registry)
# fork-granularity entry) -- a COMPILER TODO, not a bench edit.
#
# Sizes (SIZE): small (7n) expect 4219097976 (verified against a
# Bend3 C run on the cluster), big (19n) expect 1616398086 (from the
# Bend3 header, verified on the cluster in seq, par and metal modes).

type St:
  Sl{sx: U32, sy: U32, n: U32}
  Sn{l: St, r: St}

assert b2u:
  forall b: Bool
  U32

def b2u(b):
  match b:
    case False{}:
      0
    case True{}:
      1

assert prng:
  forall +x: U32
  U32

def prng(x):
  +b = U32.xor(x, U32.shln(13n, x))
  +d = U32.xor(b, U32.shrn(17n, b))
  U32.xor(d, U32.shln(5n, d))

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

assert min2:
  forall +a: U32
  forall +b: U32
  U32

def min2(a, b):
  sel(b2u(U32.is_lt(a, b)), b, a)

# squared distance from (x, y) to packed centroid c, tagged with slot k:
# d ranges to 2*1023^2 < 2^21, so d<<3|k fits comfortably
assert dst:
  forall +x: U32
  forall +y: U32
  forall +c: U32
  forall k: U32
  U32

def dst(x, y, c, k):
  +dx = sel(b2u(U32.is_lt(x, U32.and(c, 65535))), U32.sub(x, U32.and(c, 65535)), U32.sub(U32.and(c, 65535), x))
  +dy = sel(b2u(U32.is_lt(y, U32.shrn(16n, c))), U32.sub(y, U32.shrn(16n, c)), U32.sub(U32.shrn(16n, c), y))
  U32.or(U32.shln(3n, U32.add(U32.mul(dx, dx), U32.mul(dy, dy))), k)

assert szip:
  forall a: St
  forall b: St
  St

def szip(a, b):
  match a b:
    case Sl{a, b, c} Sl{d, e, f}:
      Sl{U32.add(a, d), U32.add(b, e), U32.add(c, f)}
    case Sl{a, b, c} Sn{l, r}:
      Sl{a, b, c}
    case Sn{l, r} Sl{a, b, c}:
      Sn{l, r}
    case Sn{a, b} Sn{c, d}:
      Both{l, r} = {Both{szip(a, c), szip(b, d)} : Par<St, St>}
      Sn{l, r}

# combiner: a leaf chunk folds 64 points into 24 scalar accumulators
# (8 clusters x sx/sy/n, branchless masked adds -- pure register math),
# then materializes one stats tree per chunk for the forked reduction
assert chunk:
  forall +j: Nat
  forall +i: U32
  forall +c0: U32
  forall +c1: U32
  forall +c2: U32
  forall +c3: U32
  forall +c4: U32
  forall +c5: U32
  forall +c6: U32
  forall +c7: U32
  forall s0x: U32
  forall s0y: U32
  forall s0n: U32
  forall s1x: U32
  forall s1y: U32
  forall s1n: U32
  forall s2x: U32
  forall s2y: U32
  forall s2n: U32
  forall s3x: U32
  forall s3y: U32
  forall s3n: U32
  forall s4x: U32
  forall s4y: U32
  forall s4n: U32
  forall s5x: U32
  forall s5y: U32
  forall s5n: U32
  forall s6x: U32
  forall s6y: U32
  forall s6n: U32
  forall s7x: U32
  forall s7y: U32
  forall s7n: U32
  St

def chunk(j, i, c0, c1, c2, c3, c4, c5, c6, c7, s0x, s0y, s0n, s1x, s1y, s1n, s2x, s2y, s2n, s3x, s3y, s3n, s4x, s4y, s4n, s5x, s5y, s5n, s6x, s6y, s6n, s7x, s7y, s7n):
  match j:
    case 0n:
      Sn{Sn{Sn{Sl{s0x, s0y, s0n}, Sl{s1x, s1y, s1n}}, Sn{Sl{s2x, s2y, s2n}, Sl{s3x, s3y, s3n}}},
         Sn{Sn{Sl{s4x, s4y, s4n}, Sl{s5x, s5y, s5n}}, Sn{Sl{s6x, s6y, s6n}, Sl{s7x, s7y, s7n}}}}
    case 1n+p:
      +hh = prng(U32.mul(U32.inc(U32.add(i, U32.from_nat(p))), 2654435761))
      +xx = U32.and(hh, 1023)
      +yy = U32.and(U32.shrn(16n, hh), 1023)
      +bk = U32.and(min2(min2(min2(dst(xx, yy, c0, 0), dst(xx, yy, c1, 1)),
                              min2(dst(xx, yy, c2, 2), dst(xx, yy, c3, 3))),
                         min2(min2(dst(xx, yy, c4, 4), dst(xx, yy, c5, 5)),
                              min2(dst(xx, yy, c6, 6), dst(xx, yy, c7, 7)))), 7)
      +m0 = b2u(U32.is_eq(bk, 0))
      +m1 = b2u(U32.is_eq(bk, 1))
      +m2 = b2u(U32.is_eq(bk, 2))
      +m3 = b2u(U32.is_eq(bk, 3))
      +m4 = b2u(U32.is_eq(bk, 4))
      +m5 = b2u(U32.is_eq(bk, 5))
      +m6 = b2u(U32.is_eq(bk, 6))
      +m7 = b2u(U32.is_eq(bk, 7))
      chunk(p, i, c0, c1, c2, c3, c4, c5, c6, c7,
            U32.add(s0x, U32.mul(m0, xx)), U32.add(s0y, U32.mul(m0, yy)), U32.add(s0n, m0),
            U32.add(s1x, U32.mul(m1, xx)), U32.add(s1y, U32.mul(m1, yy)), U32.add(s1n, m1),
            U32.add(s2x, U32.mul(m2, xx)), U32.add(s2y, U32.mul(m2, yy)), U32.add(s2n, m2),
            U32.add(s3x, U32.mul(m3, xx)), U32.add(s3y, U32.mul(m3, yy)), U32.add(s3n, m3),
            U32.add(s4x, U32.mul(m4, xx)), U32.add(s4y, U32.mul(m4, yy)), U32.add(s4n, m4),
            U32.add(s5x, U32.mul(m5, xx)), U32.add(s5y, U32.mul(m5, yy)), U32.add(s5n, m5),
            U32.add(s6x, U32.mul(m6, xx)), U32.add(s6y, U32.mul(m6, yy)), U32.add(s6n, m6),
            U32.add(s7x, U32.mul(m7, xx)), U32.add(s7y, U32.mul(m7, yy)), U32.add(s7n, m7))

assert pfold:
  forall +d: Nat
  forall +i: U32
  forall +c0: U32
  forall +c1: U32
  forall +c2: U32
  forall +c3: U32
  forall +c4: U32
  forall +c5: U32
  forall +c6: U32
  forall +c7: U32
  St

def pfold(d, i, c0, c1, c2, c3, c4, c5, c6, c7):
  match d:
    case 0n:
      chunk(64n, i, c0, c1, c2, c3, c4, c5, c6, c7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
    case 1n+p:
      Both{a, b} = {Both{pfold(p, i, c0, c1, c2, c3, c4, c5, c6, c7), pfold(p, U32.add(i, U32.shln(p, 64)), c0, c1, c2, c3, c4, c5, c6, c7)} : Par<St, St>}
      szip(a, b)

# new centroid from a stats leaf; an empty cluster keeps the old one
# (the divisor is forced to 1 when empty: sel picks eagerly)
assert cnew:
  forall s: St
  forall old: U32
  U32

def cnew(s, old):
  match s:
    case Sl{sx, sy, n}:
      +nn = n
      +mm = sel(b2u(U32.is_zero(nn)), nn, 1)
      sel(b2u(U32.is_zero(nn)), U32.or(U32.div(sx, mm), U32.shln(16n, U32.div(sy, mm))), old)
    case Sn{l, r}:
      old

type Cs:
  Cs{c0: U32, c1: U32, c2: U32, c3: U32, c4: U32, c5: U32, c6: U32, c7: U32}

type Tw2:
  Tw2{l: St, r: St}

# total splitter of one Sn level (the Sl row is an unreachable filler)
assert sp2:
  forall t: St
  Tw2

def sp2(t):
  match t:
    case Sn{l, r}:
      Tw2{l, r}
    case Sl{a, b, c}:
      Tw2{Sl{a, b, c}, Sl{0, 0, 0}}

assert step:
  forall d: Nat
  forall +c0: U32
  forall +c1: U32
  forall +c2: U32
  forall +c3: U32
  forall +c4: U32
  forall +c5: U32
  forall +c6: U32
  forall +c7: U32
  Cs

def step(d, c0, c1, c2, c3, c4, c5, c6, c7):
  Tw2{a, b} = sp2(pfold(Nat.sub(d, 6n), 0, c0, c1, c2, c3, c4, c5, c6, c7))
  Tw2{aa, ab} = sp2(a)
  Tw2{ba, bb} = sp2(b)
  Tw2{q0, q1} = sp2(aa)
  Tw2{q2, q3} = sp2(ab)
  Tw2{q4, q5} = sp2(ba)
  Tw2{q6, q7} = sp2(bb)
  Cs{cnew(q0, c0), cnew(q1, c1), cnew(q2, c2), cnew(q3, c3),
     cnew(q4, c4), cnew(q5, c5), cnew(q6, c6), cnew(q7, c7)}

assert loop:
  forall r: Nat
  forall +d: Nat
  forall c0: U32
  forall c1: U32
  forall c2: U32
  forall c3: U32
  forall c4: U32
  forall c5: U32
  forall c6: U32
  forall c7: U32
  U32

def loop(r, d, c0, c1, c2, c3, c4, c5, c6, c7):
  match r:
    case 0n:
      m1 = U32.add(U32.mul(c0, 2654435761), c1)
      m2 = U32.add(U32.mul(m1, 2654435761), c2)
      m3 = U32.add(U32.mul(m2, 2654435761), c3)
      m4 = U32.add(U32.mul(m3, 2654435761), c4)
      m5 = U32.add(U32.mul(m4, 2654435761), c5)
      m6 = U32.add(U32.mul(m5, 2654435761), c6)
      U32.add(U32.mul(m6, 2654435761), c7)
    case 1n+p:
      Cs{n0, n1, n2, n3, n4, n5, n6, n7} = step(d, c0, c1, c2, c3, c4, c5, c6, c7)
      loop(p, d, n0, n1, n2, n3, n4, n5, n6, n7)

assert cini:
  forall k: U32
  U32

def cini(k):
  +hh = prng(U32.add(12345, k))
  U32.or(U32.and(hh, 1023), U32.shln(16n, U32.and(U32.shrn(16n, hh), 1023)))

# one restart: 20 Lloyd rounds from this restart's random centroids
assert rst:
  forall r: U32
  forall d: Nat
  U32

def rst(r, d):
  +rr = U32.mul(r, 8)
  loop(20n, d, cini(U32.inc(rr)), cini(U32.add(rr, 2)), cini(U32.add(rr, 3)), cini(U32.add(rr, 4)), cini(U32.add(rr, 5)), cini(U32.add(rr, 6)), cini(U32.add(rr, 7)), cini(U32.add(rr, 8)))

# 64 independent restarts fork as a balanced tree (kmeans++ style
# restarts keep the machine wide across the whole run)
assert rbatch:
  forall +b: Nat
  forall +r: U32
  forall +d: Nat
  U32

def rbatch(b, r, d):
  match b:
    case 0n:
      rst(r, d)
    case 1n+p:
      Both{x, y} = {Both{rbatch(p, r, d), rbatch(p, U32.add(r, U32.shln(p, 1)), d)} : Par<U32, U32>}
      U32.add(x, y)

assert size:
  Nat

def size():
  19n

# small: size 7n expect 4219097976; big (19n) expect 1616398086
assert main:
  IO(Unit)

def main():
  IO.print(U32.show(rbatch!(6n, 0, size())))
