import Base
# Game of Life: Conway soup census on a toroidal 2^K x 2^K grid,
# ported from Bend3's par_gameoflife. The grid is an Array(k+k, U32) of
# 0/1 cells (flat, index = y*side + x); seeding tiles it with the
# source's soup generator: cell i is bit (i mod 16) of
# ((i div 16) * 2654435761). Each generation reads the current array
# and writes a fresh one; the torus wrap is a bitmask (side is a power
# of two). Checksum: pop*2654435761 + mix, where pop is the population
# count and mix folds acc*2654435761 + cell over all cells from the
# last index down to 0.
#
# Sizes: small K=3 STEPS=2 (expect 2478068852),
# big K=7 STEPS=512 (expect 2467181158, verified against the Bend3
# lineage of this benchmark).

# u32 constant from base-2^10 digits: a*2^20 + b*2^10 + c
def u32d(a: Nat, b: Nat, c: Nat) -> U32:
  U32.add(U32.shln(20n, U32.from_nat(a)), U32.add(U32.shln(10n, U32.from_nat(b)), U32.from_nat(c)))

# 2654435761 = 0x9E3779B1 (Knuth's golden-ratio multiplier)
def gol.golden() -> U32:
  u32d(2531n, 478n, 433n)

# U32 fan-out (Copy proofs erased)
def gol.u2(x: U32) -> U32 & U32:
  ((a, ea), (b, eb)) = U32.copy(x)
  (a, b)

def gol.u3(x: U32) -> U32 & (U32 & U32):
  ((a, ea), (b, eb)) = U32.copy(x)
  ((c, ec), (d, ed)) = U32.copy(b)
  (a, (c, d))

# toroidal wrap by mask = side-1: (x-1) mod side and (x+1) mod side
def gol.wrap_dec(mask: U32, x: U32) -> U32:
  ((m1, e1), (m2, e2)) = U32.copy(mask)
  U32.and(U32.add(x, m1), m2)

def gol.wrap_inc(mask: U32, x: U32) -> U32:
  U32.and(U32.inc(x), mask)

# fresh grid: 2^s cells of x
def gol.fill(s: Nat, x: U32) -> Array<U32>:
  match s:
    case 0n:
      ALeaf{x}
    case 1n+p:
      ((p1, e1), (p2, e2)) = Nat.copy(p)
      ((x1, f1), (x2, f2)) = U32.copy(x)
      ANode{gol.fill(p1, x1), gol.fill(p2, x2)}

# write cell i, dropping the swapped-out value
def gol.put(a: Array<U32>, i: U32, v: U32) -> Array<U32>:
  (a2, old) = Array.swap(U32, a, i, v)
  a2

# read cell i by double swap: park a zero, copy the value, restore it
def gol.get(a: Array<U32>, i: U32) -> Array<U32> & U32:
  ((i1, e1), (i2, e2)) = U32.copy(i)
  (a2, v) = Array.swap(U32, a, i1, U32.zero())
  ((v1, f1), (v2, f2)) = U32.copy(v)
  (a3, z) = Array.swap(U32, a2, i2, v1)
  (a3, v2)

# Conway rule: born on 3, survives on 2 or 3
def gol.next(a: U32, n: U32) -> U32:
  ((n1, e1), (n2, e2)) = U32.copy(n)
  match U32.is_eq(n1, U32.from_nat(3n)):
    case True{}:
      U32.one()
    case False{}:
      match U32.is_eq(n2, U32.from_nat(2n)):
        case True{}:
          a
        case False{}:
          U32.zero()

# update cell (y, x): 9 reads threaded through g, one write into ng;
# k is the row shift (log2 side), mask is side-1
def gol.upd(k: Nat, mask: U32, g: Array<U32>, ng: Array<U32>, y: U32, x: U32) -> Array<U32> & Array<U32>:
  ((ka, e1), (kb, e2)) = Nat.copy(k)
  ((k1, e3), (k2, e4)) = Nat.copy(kb)
  ((m1, e5), (mb, e6)) = U32.copy(mask)
  ((m2, e7), (mc, e8)) = U32.copy(mb)
  ((m3, e9), (m4, e10)) = U32.copy(mc)
  (y1, (y2, y3)) = gol.u3(y)
  (x1, (x2, x3)) = gol.u3(x)
  (ra1, (ra2, ra3)) = gol.u3(U32.shln(ka, gol.wrap_dec(m1, y1)))
  (rb1, (rb2, rb3)) = gol.u3(U32.shln(k1, y2))
  (rc1, (rc2, rc3)) = gol.u3(U32.shln(k2, gol.wrap_inc(m2, y3)))
  (xl1, (xl2, xl3)) = gol.u3(gol.wrap_dec(m3, x1))
  (xm1, (xm2, xm3)) = gol.u3(x2)
  (xr1, (xr2, xr3)) = gol.u3(gol.wrap_inc(m4, x3))
  (ci1, ci2) = gol.u2(U32.add(rb2, xm2))
  (g1, v1) = gol.get(g, U32.add(ra1, xl1))
  (g2, v2) = gol.get(g1, U32.add(ra2, xm1))
  (g3, v3) = gol.get(g2, U32.add(ra3, xr1))
  (g4, v4) = gol.get(g3, U32.add(rb1, xl2))
  (g5, v5) = gol.get(g4, U32.add(rb3, xr2))
  (g6, v6) = gol.get(g5, U32.add(rc1, xl3))
  (g7, v7) = gol.get(g6, U32.add(rc2, xm3))
  (g8, v8) = gol.get(g7, U32.add(rc3, xr3))
  (g9, alive) = gol.get(g8, ci1)
  s1 = U32.add(v1, v2)
  s2 = U32.add(v3, v4)
  s3 = U32.add(v5, v6)
  s4 = U32.add(v7, v8)
  (g9, gol.put(ng, ci2, gol.next(alive, U32.add(U32.add(s1, s2), U32.add(s3, s4)))))

# one row: fuel counts side down to 0, x counts up from 0
def gol.row(fuel: Nat, k: Nat, mask: U32, g: Array<U32>, ng: Array<U32>, y: U32, x: U32) -> Array<U32> & Array<U32>:
  match fuel:
    case 0n:
      (g, ng)
    case 1n+p:
      ((k1, e1), (k2, e2)) = Nat.copy(k)
      ((ma, e3), (mb, e4)) = U32.copy(mask)
      ((y1, e5), (y2, e6)) = U32.copy(y)
      ((x1, e7), (x2, e8)) = U32.copy(x)
      (g2, ng2) = gol.upd(k1, ma, g, ng, y1, x1)
      gol.row(p, k2, mb, g2, ng2, y2, U32.inc(x2))

# all rows: fuel counts side down to 0, y counts up from 0
def gol.rows(fuel: Nat, k: Nat, sideN: Nat, mask: U32, g: Array<U32>, ng: Array<U32>, y: U32) -> Array<U32> & Array<U32>:
  match fuel:
    case 0n:
      (g, ng)
    case 1n+p:
      ((k1, e1), (k2, e2)) = Nat.copy(k)
      ((s1, e3), (s2, e4)) = Nat.copy(sideN)
      ((ma, e5), (mb, e6)) = U32.copy(mask)
      ((y1, e7), (y2, e8)) = U32.copy(y)
      (g2, ng2) = gol.row(s1, k1, ma, g, ng, y1, U32.zero())
      gol.rows(p, k2, s2, mb, g2, ng2, U32.inc(y2))

# one generation: read g, write a fresh zero grid, drop the old one
def gol.step(k: Nat, g: Array<U32>) -> Array<U32>:
  ((ka, e1), (r1, f1)) = Nat.copy(k)
  ((kb, e2), (r2, f2)) = Nat.copy(r1)
  ((kc, e3), (r3, f3)) = Nat.copy(r2)
  ((kd, e4), (ke, f4)) = Nat.copy(r3)
  ((sa, e5), (sb, f5)) = Nat.copy(Nat.pow2(ka))
  (g2, ng2) = gol.rows(sa, kb, sb, U32.sub(U32.shln(kc, U32.one()), U32.one()), g, gol.fill(Nat.add(kd, ke), U32.zero()), U32.zero())
  ng2

def gol.run(steps: Nat, k: Nat, g: Array<U32>) -> Array<U32>:
  match steps:
    case 0n:
      g
    case 1n+p:
      ((k1, e1), (k2, e2)) = Nat.copy(k)
      gol.run(p, k2, gol.step(k1, g))

# seed cell i: bit (i mod 16) of soup hash ((i div 16) * golden)
def gol.seed_val(i: U32, gld: U32) -> U32:
  ((a, ea), (b, eb)) = U32.copy(i)
  h = U32.mul(U32.shrn(4n, a), gld)
  kk = U32.to_nat(U32.and(b, U32.from_nat(15n)))
  U32.and(U32.shrn(kk, h), U32.one())

def gol.seed(fuel: Nat, g: Array<U32>, i: U32, gld: U32) -> Array<U32>:
  match fuel:
    case 0n:
      g
    case 1n+p:
      ((i1, e1), (i2, e2)) = U32.copy(i)
      ((i3, e3), (i4, e4)) = U32.copy(i2)
      ((ga, f1), (gb, f2)) = U32.copy(gld)
      gol.seed(p, gol.put(g, i1, gol.seed_val(i3, ga)), U32.inc(i4), gb)

# positional board hash: acc = acc*golden + cell, from the last cell
# down to cell 0 (the source's fold order)
def gol.mix(fuel: Nat, g: Array<U32>, i: U32, acc: U32, gld: U32) -> Array<U32> & U32:
  match fuel:
    case 0n:
      (g, acc)
    case 1n+p:
      ((i1, e1), (i2, e2)) = U32.copy(i)
      ((ga, f1), (gb, f2)) = U32.copy(gld)
      (g2, v) = gol.get(g, i1)
      gol.mix(p, g2, U32.sub(i2, U32.one()), U32.add(U32.mul(acc, ga), v), gb)

# population count: sum every cell
def gol.sum(a: Array<U32>) -> U32:
  match a:
    case ALeaf{x}:
      x
    case ANode{xs, ys}:
      U32.add(gol.sum(xs), gol.sum(ys))

# checksum: pop*golden + mix, as the source's census mixing
def gol.bench(k: Nat, steps: Nat) -> U32:
  ((k1, e1), (kr1, f1)) = Nat.copy(k)
  ((k2, e2), (kr2, f2)) = Nat.copy(kr1)
  ((k3, e3), (kr3, f3)) = Nat.copy(kr2)
  ((k4, e4), (k5, f4)) = Nat.copy(kr3)
  ((d1, e5), (d2, f5)) = Nat.copy(Nat.add(k1, k2))
  ((c1, e6), (c2, f6)) = Nat.copy(Nat.pow2(d1))
  ((ga, e7), (gb, f7)) = U32.copy(gol.golden())
  ((gc, e8), (gd, f8)) = U32.copy(gb)
  (g2, mixv) = gol.mix(c2, gol.run(steps, k5, gol.seed(c1, gol.fill(d2, U32.zero()), U32.zero(), ga)), U32.sub(U32.shln(Nat.add(k3, k4), U32.one()), U32.one()), U32.zero(), gc)
  U32.add(U32.mul(gol.sum(g2), gd), mixv)

# (K, STEPS)
def size.small() -> Nat & Nat:
  (3n, 2n)

def expect.small() -> U32:
  u32d(2363n, 277n, 116n)

def size.big() -> Nat & Nat:
  (7n, 512n)

def expect.big() -> U32:
  u32d(2352n, 908n, 614n)

def main() -> Bool:
  (k, s) = size.small()
  U32.is_eq(gol.bench(k, s), expect.small())
