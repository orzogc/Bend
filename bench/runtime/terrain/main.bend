import Base
# terrain: procedural terrain tile pipeline, ported 1-to-1 from Bend3's
# par_terrain -- the suite's array write/read stress case. 2^SIZE
# independent 64x64 tiles fork as a balanced tree; each tile fills its
# own 4096-slot heightmap with bilinear value noise (8.8 fixed-point
# lattice hashes, one array write per cell), runs EPASS in-place
# thermal-relaxation sweeps (each cell reads itself and its 4 clamped
# neighbours, Gauss-Seidel scan order, plus a pass-salted 1-bit
# roughening so the field never converges), then buckets every cell
# into a 64-bin height histogram (read + bump) and folds map and
# histogram into a position-weighted scalar; tile scalars sum up the
# fork tree. Knobs: SIZE (2^SIZE tiles, 2x per notch), EPASS
# (relaxation sweeps per tile, the fine linear knob).
#
# NO TUNING: this file is the elegant spelling BY LAW (bench.ts
# header). A register-threading rewrite of the erode sweep (carrying
# prev/cur across the recursion to cut 2 array reads, cca3d150) was
# REVERTED on Taelin's order 2026-07-24: it tuned the bench, not the
# compiler. The sweep's memory-bound GPU profile is the honest result.
#
# Port deviations from the Bend3 source (semantics preserved exactly):
# - `h[i]` reads become Array.get(U32, h, i), `h[i] <- v` writes become
#   Array.swap(U32, h, i, v); both hand the array back.
# - Bend3's flat literal `![4095:0, _:0; 4096]` becomes
#   [0 : U32 * 12n] (the C backend lays it flat in one block).
# - Cell, sweep and depth counters are Nats (no U32 match in Bend4);
#   the pass salt `1+p` reads back as U32.inc(U32.from_nat(p)).
# - `(xc > 0)` as a 0/1 word becomes b2u(U32.is_gt(xc, 0)).
# - Words used twice ride `+` binders (Bend3 auto-copied them). A
#   tuple pattern cannot bind `+`, so hist hands the height it read
#   twice on to a continuation def (hist_go).
#
# Sizes (SIZE, EPASS): small (4n, 5n) expect 4236200168 (verified
# against a Bend3 C run on the cluster), big (16n, 5n) expect
# 2572468224 (the Bend3 header's number, re-verified on the cluster).

law b2u:
  for b: Bool
  U32

def b2u(b):
  match b:
    case False{}:
      0
    case True{}:
      1

law prng:
  for +x: U32
  U32

def prng(x):
  +b = U32.xor(x, U32.shln(x, 13n))
  +d = U32.xor(b, U32.shrn(b, 17n))
  U32.xor(d, U32.shln(d, 5n))

# lattice corner hash -> 0..255
law hsh:
  for gx: U32
  for gz: U32
  U32

def hsh(gx, gz):
  U32.and(prng(U32.xor(U32.mul(gx, 2654435761), U32.mul(gz, 340573321))), 255)

# value noise at 8.8 fixed-point (x, z): bilinear lerp of 4 corner
# hashes
law ground:
  for +x: U32
  for +z: U32
  U32

def ground(x, z):
  +gx = U32.and(U32.shrn(x, 8n), 63)
  +gz = U32.and(U32.shrn(z, 8n), 63)
  +fx = U32.and(x, 255)
  +fz = U32.and(z, 255)
  +gx1 = U32.and(U32.inc(gx), 63)
  +gz1 = U32.and(U32.inc(gz), 63)
  h00 = hsh(gx, gz)
  h10 = hsh(gx1, gz)
  h01 = hsh(gx, gz1)
  h11 = hsh(gx1, gz1)
  t0 = U32.shrn(U32.add(U32.mul(h00, U32.sub(256, fx)), U32.mul(h10, fx)), 8n)
  t1 = U32.shrn(U32.add(U32.mul(h01, U32.sub(256, fx)), U32.mul(h11, fx)), 8n)
  U32.shrn(U32.add(U32.mul(t0, U32.sub(256, fz)), U32.mul(t1, fz)), 8n)

# noise-fill one tile: one write per cell, sampled at 64 sub-lattice
# units per cell from the tile's world offset
law fill:
  for +j: Nat
  for +ox: U32
  for +oz: U32
  for r: Array<U32> & U32
  Array<U32>

def fill(j, ox, oz, r):
  match j:
    case 0n:
      (h, z) = r
      h
    case 1n+q:
      (h, z) = r
      +i = U32.sub(4096, U32.inc(U32.from_nat(q)))
      +g = ground(U32.shln(U32.add(ox, U32.and(i, 63)), 6n), U32.shln(U32.add(oz, U32.shrn(i, 6n)), 6n))
      fill(q, ox, oz, Array.swap(U32, h, i, g))

# one relaxation cell: 5 reads + 1 write; neighbours clamp at the tile
# edge; the pass-salted bit keeps the field from ever converging.
# four cells unroll per erode turn: every Array op rides inline in
# the next stage def's argument, so the whole 24-op chain fuses into
# one machine segment; only the last write's pair crosses back into
# the erode spin, destructured as the r column of the next turn
law erode.f5:
  for +i: U32
  for +p: U32
  for hc: U32
  for hl: U32
  for hr: U32
  for hu: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.f5(i, p, hc, hl, hr, hu, r):
  (h5, hd) = r
  +rough = U32.and(prng(U32.xor(i, U32.mul(p, 2654435761))), 1)
  +nv = U32.add(U32.shrn(U32.add(U32.add(U32.add(U32.add(U32.mul(hc, 4), hl), hr), hu), hd), 3n), rough)
  Array.swap(U32, h5, i, nv)

law erode.f4:
  for +i: U32
  for +p: U32
  for +zc: U32
  for hc: U32
  for hl: U32
  for hr: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.f4(i, p, zc, hc, hl, hr, r):
  (h4, hu) = r
  erode.f5(i, p, hc, hl, hr, hu, Array.get(U32, h4, U32.add(i, U32.shln(b2u(U32.is_lt(zc, 63)), 6n))))

law erode.f3:
  for +i: U32
  for +p: U32
  for +zc: U32
  for hc: U32
  for hl: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.f3(i, p, zc, hc, hl, r):
  (h3, hr) = r
  erode.f4(i, p, zc, hc, hl, hr, Array.get(U32, h3, U32.sub(i, U32.shln(b2u(U32.is_gt(zc, 0)), 6n))))

law erode.f2:
  for +i: U32
  for +p: U32
  for +xc: U32
  for +zc: U32
  for hc: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.f2(i, p, xc, zc, hc, r):
  (h2, hl) = r
  erode.f3(i, p, zc, hc, hl, Array.get(U32, h2, U32.add(i, b2u(U32.is_lt(xc, 63)))))

law erode.f1:
  for +i: U32
  for +p: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.f1(i, p, r):
  (h1, hc) = r
  +xc = U32.and(i, 63)
  +zc = U32.shrn(i, 6n)
  erode.f2(i, p, xc, zc, hc, Array.get(U32, h1, U32.sub(i, b2u(U32.is_gt(xc, 0)))))

law erode.f0:
  for +i: U32
  for +p: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.f0(i, p, r):
  (h0, old) = r
  erode.f1(i, p, Array.get(U32, h0, i))

law erode.d5:
  for +i: U32
  for +p: U32
  for hc: U32
  for hl: U32
  for hr: U32
  for hu: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.d5(i, p, hc, hl, hr, hu, r):
  (h5, hd) = r
  +rough = U32.and(prng(U32.xor(i, U32.mul(p, 2654435761))), 1)
  +nv = U32.add(U32.shrn(U32.add(U32.add(U32.add(U32.add(U32.mul(hc, 4), hl), hr), hu), hd), 3n), rough)
  erode.f0(U32.inc(i), p, Array.swap(U32, h5, i, nv))

law erode.d4:
  for +i: U32
  for +p: U32
  for +zc: U32
  for hc: U32
  for hl: U32
  for hr: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.d4(i, p, zc, hc, hl, hr, r):
  (h4, hu) = r
  erode.d5(i, p, hc, hl, hr, hu, Array.get(U32, h4, U32.add(i, U32.shln(b2u(U32.is_lt(zc, 63)), 6n))))

law erode.d3:
  for +i: U32
  for +p: U32
  for +zc: U32
  for hc: U32
  for hl: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.d3(i, p, zc, hc, hl, r):
  (h3, hr) = r
  erode.d4(i, p, zc, hc, hl, hr, Array.get(U32, h3, U32.sub(i, U32.shln(b2u(U32.is_gt(zc, 0)), 6n))))

law erode.d2:
  for +i: U32
  for +p: U32
  for +xc: U32
  for +zc: U32
  for hc: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.d2(i, p, xc, zc, hc, r):
  (h2, hl) = r
  erode.d3(i, p, zc, hc, hl, Array.get(U32, h2, U32.add(i, b2u(U32.is_lt(xc, 63)))))

law erode.d1:
  for +i: U32
  for +p: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.d1(i, p, r):
  (h1, hc) = r
  +xc = U32.and(i, 63)
  +zc = U32.shrn(i, 6n)
  erode.d2(i, p, xc, zc, hc, Array.get(U32, h1, U32.sub(i, b2u(U32.is_gt(xc, 0)))))

law erode.d0:
  for +i: U32
  for +p: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.d0(i, p, r):
  (h0, old) = r
  erode.d1(i, p, Array.get(U32, h0, i))

law erode.b5:
  for +i: U32
  for +p: U32
  for hc: U32
  for hl: U32
  for hr: U32
  for hu: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.b5(i, p, hc, hl, hr, hu, r):
  (h5, hd) = r
  +rough = U32.and(prng(U32.xor(i, U32.mul(p, 2654435761))), 1)
  +nv = U32.add(U32.shrn(U32.add(U32.add(U32.add(U32.add(U32.mul(hc, 4), hl), hr), hu), hd), 3n), rough)
  erode.d0(U32.inc(i), p, Array.swap(U32, h5, i, nv))

law erode.b4:
  for +i: U32
  for +p: U32
  for +zc: U32
  for hc: U32
  for hl: U32
  for hr: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.b4(i, p, zc, hc, hl, hr, r):
  (h4, hu) = r
  erode.b5(i, p, hc, hl, hr, hu, Array.get(U32, h4, U32.add(i, U32.shln(b2u(U32.is_lt(zc, 63)), 6n))))

law erode.b3:
  for +i: U32
  for +p: U32
  for +zc: U32
  for hc: U32
  for hl: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.b3(i, p, zc, hc, hl, r):
  (h3, hr) = r
  erode.b4(i, p, zc, hc, hl, hr, Array.get(U32, h3, U32.sub(i, U32.shln(b2u(U32.is_gt(zc, 0)), 6n))))

law erode.b2:
  for +i: U32
  for +p: U32
  for +xc: U32
  for +zc: U32
  for hc: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.b2(i, p, xc, zc, hc, r):
  (h2, hl) = r
  erode.b3(i, p, zc, hc, hl, Array.get(U32, h2, U32.add(i, b2u(U32.is_lt(xc, 63)))))

law erode.b1:
  for +i: U32
  for +p: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.b1(i, p, r):
  (h1, hc) = r
  +xc = U32.and(i, 63)
  +zc = U32.shrn(i, 6n)
  erode.b2(i, p, xc, zc, hc, Array.get(U32, h1, U32.sub(i, b2u(U32.is_gt(xc, 0)))))

law erode.b0:
  for +i: U32
  for +p: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.b0(i, p, r):
  (h0, old) = r
  erode.b1(i, p, Array.get(U32, h0, i))

law erode.a5:
  for +i: U32
  for +p: U32
  for hc: U32
  for hl: U32
  for hr: U32
  for hu: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.a5(i, p, hc, hl, hr, hu, r):
  (h5, hd) = r
  +rough = U32.and(prng(U32.xor(i, U32.mul(p, 2654435761))), 1)
  +nv = U32.add(U32.shrn(U32.add(U32.add(U32.add(U32.add(U32.mul(hc, 4), hl), hr), hu), hd), 3n), rough)
  erode.b0(U32.inc(i), p, Array.swap(U32, h5, i, nv))

law erode.a4:
  for +i: U32
  for +p: U32
  for +zc: U32
  for hc: U32
  for hl: U32
  for hr: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.a4(i, p, zc, hc, hl, hr, r):
  (h4, hu) = r
  erode.a5(i, p, hc, hl, hr, hu, Array.get(U32, h4, U32.add(i, U32.shln(b2u(U32.is_lt(zc, 63)), 6n))))

law erode.a3:
  for +i: U32
  for +p: U32
  for +zc: U32
  for hc: U32
  for hl: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.a3(i, p, zc, hc, hl, r):
  (h3, hr) = r
  erode.a4(i, p, zc, hc, hl, hr, Array.get(U32, h3, U32.sub(i, U32.shln(b2u(U32.is_gt(zc, 0)), 6n))))

law erode.a2:
  for +i: U32
  for +p: U32
  for +xc: U32
  for +zc: U32
  for hc: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.a2(i, p, xc, zc, hc, r):
  (h2, hl) = r
  erode.a3(i, p, zc, hc, hl, Array.get(U32, h2, U32.add(i, b2u(U32.is_lt(xc, 63)))))

law erode.a1:
  for +i: U32
  for +p: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def erode.a1(i, p, r):
  (h1, hc) = r
  +xc = U32.and(i, 63)
  +zc = U32.shrn(i, 6n)
  erode.a2(i, p, xc, zc, hc, Array.get(U32, h1, U32.sub(i, b2u(U32.is_gt(xc, 0)))))

law erode.go:
  for +i: U32
  for +p: U32
  for h: Array<U32>
  Array<U32> & U32

def erode.go(i, p, h):
  erode.a1(i, p, Array.get(U32, h, i))

# one Gauss-Seidel sweep over the tile, ascending scan order, four
# cells per turn (j counts quads); the quad's final write pair rides
# into the next turn as the r column
law erode:
  for +j: Nat
  for +p: U32
  for r: Array<U32> & U32
  Array<U32>

def erode(j, p, r):
  match j:
    case 0n:
      (h, z) = r
      h
    case 1n+q:
      (h, z) = r
      +i = U32.sub(4096, U32.shln(U32.inc(U32.from_nat(q)), 2n))
      erode(q, p, erode.go(i, p, h))

law smooth:
  for +p: Nat
  for h: Array<U32>
  Array<U32>

def smooth(p, h):
  match p:
    case 0n:
      h
    case 1n+q:
      h2 = erode(1024n, U32.inc(U32.from_nat(q)), (h, 0))
      smooth(q, h2)

# histogram fold: mix every bucket count, position-weighted; the
# current read rides in as the (array, count) pair r, and each step
# issues the next read (the final step issues one masked dead read)
law gfold:
  for +j: Nat
  for r: Array<U32> & U32
  for acc: U32
  U32

def gfold(j, r, acc):
  match j:
    case 0n:
      acc
    case 1n+q:
      (g2, c) = r
      +i = U32.sub(63, U32.from_nat(q))
      gfold(q, Array.get(U32, g2, U32.inc(i)), U32.xor(U32.mul(acc, 2654435761), U32.mul(c, U32.add(i, 3))))

# bucket increment: the (array, count) read pair arrives as a
# parameter and the bumped bucket's write pair is handed back
law hist.bump:
  for +b: U32
  for r: Array<U32> & U32
  Array<U32> & U32

def hist.bump(b, r):
  (g2, c) = r
  Array.swap(U32, g2, b, U32.inc(c))

# per cell: read the height, bump its histogram bucket, mix the height
# into the running position-weighted checksum; the current height read
# rides in as the pair r (the final step issues one masked dead read)
law hist:
  for +j: Nat
  for r: Array<U32> & U32
  for rg: Array<U32> & U32
  for acc: U32
  U32

def hist(j, r, rg, acc):
  match j:
    case 0n:
      (g, z) = rg
      gfold(64n, Array.get(U32, g, 0), acc)
    case 1n+q:
      (h2, +v) = r
      (g, z) = rg
      +i = U32.sub(4095, U32.from_nat(q))
      +b = U32.and(U32.shrn(v, 2n), 63)
      hist(q, Array.get(U32, h2, U32.inc(i)), hist.bump(b, Array.get(U32, g, b)),
        U32.add(U32.mul(acc, 2654435761), U32.mul(v, U32.inc(i))))

# one tile: fill, EPASS relaxation sweeps, histogram + fold
law tile:
  for +t: U32
  for e: Nat
  U32

def tile(t, e):
  a = [0 : U32 * 12n]
  h0 = fill(4096n, U32.shln(U32.and(t, 255), 6n), U32.shln(U32.shrn(t, 8n), 6n), (a, 0))
  h1 = smooth(e, h0)
  b = [0 : U32 * 6n]
  hist(4096n, Array.get(U32, h1, 0), (b, 0), U32.inc(t))

law batch:
  for +d: Nat
  for +t: U32
  for +e: Nat
  U32

def batch(d, t, e):
  match d:
    case 0n:
      tile(t, e)
    case 1n+q:
      a b = batch(q, t, e) batch(q, U32.add(t, U32.shln(1, q)), e)
      U32.add(a, b)

law size:
  Nat

def size():
  16n

law epass:
  Nat

def epass():
  5n

# small: batch!(4n, 0, epass()) expect 4236200168; big batch!(size(), 0,
# epass()) expect 2572468224
law main:
  IO(Unit)

def main():
  IO.print(U32.show(batch!(size(), 0, epass())))
