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
# - `h[i]` reads become Array.get(h, i), `h[i] <- v` writes become
#   Array.swap(U32, h, i, v); both hand the array back.
# - Bend3's flat literal `![4095:0, _:0; 4096]` becomes
#   Array.new(12n, 0) (the C backend lays it flat in one block).
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
  forall +x: +U32
  U32

def prng(x):
  +b = {U32.xor(x, U32.shln(13n, x)) : +U32}
  +d = {U32.xor(b, U32.shrn(17n, b)) : +U32}
  U32.xor(d, U32.shln(5n, d))

# lattice corner hash -> 0..255
assert hsh:
  forall gx: U32
  forall gz: U32
  U32

def hsh(gx, gz):
  U32.and(prng(U32.xor(U32.mul(gx, 2654435761), U32.mul(gz, 340573321))), 255)

# value noise at 8.8 fixed-point (x, z): bilinear lerp of 4 corner
# hashes
assert ground:
  forall +x: +U32
  forall +z: +U32
  U32

def ground(x, z):
  +gx = {U32.and(U32.shrn(8n, x), 63) : +U32}
  +gz = {U32.and(U32.shrn(8n, z), 63) : +U32}
  +fx = {U32.and(x, 255) : +U32}
  +fz = {U32.and(z, 255) : +U32}
  +gx1 = {U32.and(U32.inc(gx), 63) : +U32}
  +gz1 = {U32.and(U32.inc(gz), 63) : +U32}
  h00 = hsh(gx, gz)
  h10 = hsh(gx1, gz)
  h01 = hsh(gx, gz1)
  h11 = hsh(gx1, gz1)
  t0 = U32.shrn(8n, U32.add(U32.mul(h00, U32.sub(256, fx)), U32.mul(h10, fx)))
  t1 = U32.shrn(8n, U32.add(U32.mul(h01, U32.sub(256, fx)), U32.mul(h11, fx)))
  U32.shrn(8n, U32.add(U32.mul(t0, U32.sub(256, fz)), U32.mul(t1, fz)))

# noise-fill one tile: one write per cell, sampled at 64 sub-lattice
# units per cell from the tile's world offset
assert fill:
  forall +j: +Nat
  forall +ox: +U32
  forall +oz: +U32
  forall h: Array<U32>
  Array<U32>

def fill(j, ox, oz, h):
  match j:
    case 0n:
      h
    case 1n+q:
      +i = {U32.sub(4096, U32.inc(U32.from_nat(q))) : +U32}
      +g = {ground(U32.shln(6n, U32.add(ox, U32.and(i, 63))), U32.shln(6n, U32.add(oz, U32.shrn(6n, i)))) : +U32}
      (h2, z) = Array.swap(U32, h, i, g)
      fill(q, ox, oz, h2)

# one relaxation cell: 5 reads + 1 write; neighbours clamp at the tile
# edge; the pass-salted bit keeps the field from ever converging
# one Gauss-Seidel sweep over the tile, ascending scan order; the
# whole cell update rides this one self-tail segment
assert erode:
  forall +j: +Nat
  forall +p: +U32
  forall h: Array<U32>
  Array<U32>

def erode(j, p, h):
  match j:
    case 0n:
      h
    case 1n+q:
      +i = {U32.sub(4096, U32.inc(U32.from_nat(q))) : +U32}
      +xc = {U32.and(i, 63) : +U32}
      +zc = {U32.shrn(6n, i) : +U32}
      (h1, hc) = Array.get(h, i)
      (h2, hl) = Array.get(h1, U32.sub(i, b2u(U32.is_gt(xc, 0))))
      (h3, hr) = Array.get(h2, U32.add(i, b2u(U32.is_lt(xc, 63))))
      (h4, hu) = Array.get(h3, U32.sub(i, U32.shln(6n, b2u(U32.is_gt(zc, 0)))))
      (h5, hd) = Array.get(h4, U32.add(i, U32.shln(6n, b2u(U32.is_lt(zc, 63)))))
      +rough = {U32.and(prng(U32.xor(i, U32.mul(p, 2654435761))), 1) : +U32}
      +nv = {U32.add(U32.shrn(3n, U32.add(U32.add(U32.add(U32.add(U32.mul(hc, 4), hl), hr), hu), hd)), rough) : +U32}
      (h6, old) = Array.swap(U32, h5, i, nv)
      erode(q, p, h6)

assert smooth:
  forall +p: +Nat
  forall h: Array<U32>
  Array<U32>

def smooth(p, h):
  match p:
    case 0n:
      h
    case 1n+q:
      h2 = erode(4096n, U32.inc(U32.from_nat(q)), h)
      smooth(q, h2)

# histogram fold: mix every bucket count, position-weighted
assert gfold:
  forall +j: +Nat
  forall g: Array<U32>
  forall acc: U32
  U32

def gfold(j, g, acc):
  match j:
    case 0n:
      acc
    case 1n+q:
      +i = {U32.sub(64, U32.inc(U32.from_nat(q))) : +U32}
      (g2, c) = Array.get(g, i)
      gfold(q, g2, U32.xor(U32.mul(acc, 2654435761), U32.mul(c, U32.add(i, 3))))

# per cell: read the height, bump its histogram bucket, mix the height
# into the running position-weighted checksum
assert hist:
  forall +j: +Nat
  forall h: Array<U32>
  forall g: Array<U32>
  forall acc: U32
  U32

def hist(j, h, g, acc):
  match j:
    case 0n:
      gfold(64n, g, acc)
    case 1n+q:
      +i = {U32.sub(4096, U32.inc(U32.from_nat(q))) : +U32}
      (h2, v0) = Array.get(h, i)
      +v = {v0 : +U32}
      +b = {U32.and(U32.shrn(2n, v), 63) : +U32}
      (g2, c) = Array.get(g, b)
      (g3, z) = Array.swap(U32, g2, b, U32.inc(c))
      hist(q, h2, g3, U32.add(U32.mul(acc, 2654435761), U32.mul(v, U32.inc(i))))

# one tile: fill, EPASS relaxation sweeps, histogram + fold
assert tile:
  forall +t: +U32
  forall e: Nat
  U32

def tile(t, e):
  a = Array.new(12n, 0)
  h0 = fill(4096n, U32.shln(6n, U32.and(t, 255)), U32.shln(6n, U32.shrn(8n, t)), a)
  h1 = smooth(e, h0)
  b = Array.new(6n, 0)
  hist(4096n, h1, b, U32.inc(t))

assert batch:
  forall +d: +Nat
  forall +t: +U32
  forall +e: +Nat
  U32

def batch(d, t, e):
  match d:
    case 0n:
      tile(t, e)
    case 1n+q:
      Both{a, b} = {Both{batch(q, t, e), batch(q, U32.add(t, U32.shln(q, 1)), e)} : Par<U32, U32>}
      U32.add(a, b)

assert size:
  Nat

def size():
  16n

assert epass:
  Nat

def epass():
  5n

# small: batch!(4n, 0, epass()) expect 4236200168; big batch!(size(), 0,
# epass()) expect 2572468224
assert main:
  IO(Unit)

def main():
  IO.print(U32.show(batch!(size(), 0, epass())))
