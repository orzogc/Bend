#[halts]
import Base
# Raytrace: parallel recursive sphere raytracer, all f32, ported
# 1-to-1 from Bend3's par_raytrace. Fixed scene of 9 spheres (one
# 10000-radius floor sphere, six scene balls, two mirrored back-row
# balls) + one point light at (-3,8,1), camera at the origin looking
# +z. Per pixel: 2x2 supersampling -- four primary rays through the
# pixel corners at (0.25,0.75) offsets; each ray runs trace in
# accumulator form (acc, w): per mirror bounce acc' = acc +
# ((w*lum)*(1-kr)), w' = w*kr, final level adds acc + (w*lum). The
# nearest-hit search is the recursive min-fold nearest: isect
# (quadratic solve + sqrt, near root only) over spheres 8 down to 0
# with strict <. The pixel quantizes the averaged luminance to
# f2u(255*clamp01(avg)). rowf forks the 2^ROWS image rows as a
# balanced tree and colf forks 2^14 columns under each row, one
# per-pixel leaf (columns past width contribute 0). Checksum = u32
# wrapping sum over all pixels. Sphere indices and depth counters are
# Nats (no U32 match in Bend4); float literals spell as fl(n, d), one
# correctly rounded conversion, bit-exact vs the C literal; the
# compute-then-match stages of trace and clamp01 ride continuation
# defs. nearest is ONE self-tail def: the sphere table rides four
# small pure-word selectors (sx sy sz sr) and the quadratic rides
# isect5, so tocl splices them all and the whole nine-sphere fold
# compiles to a single machine segment -- no Sph ctor, no isect
# call, no nearest.go hop.
# Knobs: rows = 12 (2^12 = 4096 image rows, coarse), width (fine,
# <= 2^14).
#
# Sizes (rows, width): small (6, 80) expect 402971 (verified against
# a Bend3 C run on the cluster), big (12, 6000) expect 1924309504
# (from the Bend3 header).

type Sph:
  Sph{x: F32, y: F32, z: F32, r: F32, kr: F32}

type Hit:
  Hit{t: F32, i: U32}

# float literal n/d (Bend4 has no float literal syntax)
assert fl:
  forall n: U32
  forall d: U32
  F32

def fl(n, d):
  F32.div(U32.to_f32(n), U32.to_f32(d))

assert sphere:
  forall i: Nat
  Sph

def sphere(i):
  match i:
    case 0n:
      Sph{U32.to_f32(0), F32.sub(U32.to_f32(0), U32.to_f32(10001)), U32.to_f32(5), U32.to_f32(10000), fl(3, 10)}
    case 1n:
      Sph{U32.to_f32(0), U32.to_f32(0), U32.to_f32(5), U32.to_f32(1), fl(7, 10)}
    case 2n:
      Sph{U32.to_f32(2), fl(5, 10), U32.to_f32(6), U32.to_f32(1), fl(4, 10)}
    case 3n:
      Sph{F32.sub(U32.to_f32(0), U32.to_f32(2)), fl(5, 10), U32.to_f32(6), U32.to_f32(1), fl(4, 10)}
    case 4n:
      Sph{U32.to_f32(1), F32.sub(U32.to_f32(0), fl(6, 10)), fl(35, 10), fl(4, 10), fl(9, 10)}
    case 5n:
      Sph{F32.sub(U32.to_f32(0), U32.to_f32(1)), F32.sub(U32.to_f32(0), fl(6, 10)), fl(35, 10), fl(4, 10), fl(9, 10)}
    case 6n:
      Sph{U32.to_f32(0), fl(16, 10), U32.to_f32(7), fl(12, 10), fl(1, 10)}
    case 7n:
      Sph{fl(35, 10), fl(2, 10), U32.to_f32(8), U32.to_f32(1), fl(6, 10)}
    case 8n+k:
      Sph{F32.sub(U32.to_f32(0), fl(35, 10)), fl(2, 10), U32.to_f32(8), U32.to_f32(1), fl(6, 10)}

# ray-sphere: t of the near root, or 1e9 for a miss (disc < 0 or t < eps)
assert isect5:
  forall cx: F32
  forall cy: F32
  forall cz: F32
  forall r: F32
  forall ox: F32
  forall oy: F32
  forall oz: F32
  forall dx: F32
  forall dy: F32
  forall dz: F32
  F32

def isect5(cx, cy, cz, r, ox, oy, oz, dx, dy, dz):
  +px = F32.sub(ox, cx)
  +py = F32.sub(oy, cy)
  +pz = F32.sub(oz, cz)
  +rr = r
  +b = F32.add(F32.add(F32.mul(px, dx), F32.mul(py, dy)), F32.mul(pz, dz))
  isect.go(b, F32.sub(F32.mul(b, b), F32.sub(F32.add(F32.add(F32.mul(px, px), F32.mul(py, py)), F32.mul(pz, pz)), F32.mul(rr, rr))))

assert sx:
  forall i: Nat
  F32

def sx(i):
  match i:
    case 0n: U32.to_f32(0)
    case 1n: U32.to_f32(0)
    case 2n: U32.to_f32(2)
    case 3n: F32.sub(U32.to_f32(0), U32.to_f32(2))
    case 4n: U32.to_f32(1)
    case 5n: F32.sub(U32.to_f32(0), U32.to_f32(1))
    case 6n: U32.to_f32(0)
    case 7n: fl(35, 10)
    case 8n+k: F32.sub(U32.to_f32(0), fl(35, 10))

assert sy:
  forall i: Nat
  F32

def sy(i):
  match i:
    case 0n: F32.sub(U32.to_f32(0), U32.to_f32(10001))
    case 1n: U32.to_f32(0)
    case 2n: fl(5, 10)
    case 3n: fl(5, 10)
    case 4n: F32.sub(U32.to_f32(0), fl(6, 10))
    case 5n: F32.sub(U32.to_f32(0), fl(6, 10))
    case 6n: fl(16, 10)
    case 7n: fl(2, 10)
    case 8n+k: fl(2, 10)

assert sz:
  forall i: Nat
  F32

def sz(i):
  match i:
    case 0n: U32.to_f32(5)
    case 1n: U32.to_f32(5)
    case 2n: U32.to_f32(6)
    case 3n: U32.to_f32(6)
    case 4n: fl(35, 10)
    case 5n: fl(35, 10)
    case 6n: U32.to_f32(7)
    case 7n: U32.to_f32(8)
    case 8n+k: U32.to_f32(8)

assert sr:
  forall i: Nat
  F32

def sr(i):
  match i:
    case 0n: U32.to_f32(10000)
    case 1n: U32.to_f32(1)
    case 2n: U32.to_f32(1)
    case 3n: U32.to_f32(1)
    case 4n: fl(4, 10)
    case 5n: fl(4, 10)
    case 6n: fl(12, 10)
    case 7n: U32.to_f32(1)
    case 8n+k: U32.to_f32(1)

assert isect.go:
  forall b: F32
  forall +disc: F32
  F32

def isect.go(b, disc):
  match F32.is_lt(disc, U32.to_f32(0)):
    case False{}:
      isect.t(F32.sub(F32.sub(U32.to_f32(0), b), F32.sqrt(disc)))
    case True{}:
      U32.to_f32(1000000000)

assert isect.t:
  forall +t: F32
  F32

def isect.t(t):
  match F32.is_lt(t, fl(1, 1000)):
    case False{}:
      t
    case True{}:
      U32.to_f32(1000000000)

# nearest hit: recursive min-fold over the spheres, testing 8 down to
# 0 with strict <
assert nearest:
  forall +i: Nat
  forall +ox: F32
  forall +oy: F32
  forall +oz: F32
  forall +dx: F32
  forall +dy: F32
  forall +dz: F32
  forall +bt: F32
  forall bi: U32
  Hit

def nearest(i, ox, oy, oz, dx, dy, dz, bt, bi):
  match i:
    case 0n:
      Hit{bt, bi}
    case 1n+k:
      +kk = k
      +t = isect5(sx(kk), sy(kk), sz(kk), sr(kk), ox, oy, oz, dx, dy, dz)
      match F32.is_lt(t, bt):
        case False{}:
          nearest(kk, ox, oy, oz, dx, dy, dz, bt, bi)
        case True{}:
          nearest(kk, ox, oy, oz, dx, dy, dz, t, U32.from_nat(kk))

assert fmax0:
  forall +x: F32
  F32

def fmax0(x):
  match F32.is_lt(x, U32.to_f32(0)):
    case False{}:
      x
    case True{}:
      U32.to_f32(0)

# diffuse term, zeroed when the shadow ray hits something before the light
assert shade:
  forall st: F32
  forall ll: F32
  forall df: F32
  F32

def shade(st, ll, df):
  match F32.is_lt(st, ll):
    case False{}:
      df
    case True{}:
      U32.to_f32(0)

assert clamp01.hi:
  forall +x: F32
  F32

def clamp01.hi(x):
  match F32.is_lt(U32.to_f32(1), x):
    case False{}:
      x
    case True{}:
      U32.to_f32(1)

assert clamp01:
  forall +x: F32
  F32

def clamp01(x):
  match F32.is_lt(x, U32.to_f32(0)):
    case False{}:
      clamp01.hi(x)
    case True{}:
      U32.to_f32(0)

assert trace:
  forall dep: Nat
  forall +ox: F32
  forall +oy: F32
  forall +oz: F32
  forall +dx: F32
  forall +dy: F32
  forall +dz: F32
  forall acc: F32
  forall w: F32
  F32

def trace(dep, ox, oy, oz, dx, dy, dz, acc, w):
  match nearest(9n, ox, oy, oz, dx, dy, dz, U32.to_f32(1000000000), 9):
    case Hit{t, id}:
      trace.hit(id, t, dep, ox, oy, oz, dx, dy, dz, acc, w)

assert trace.hit:
  forall +id: U32
  forall t: F32
  forall dep: Nat
  forall ox: F32
  forall oy: F32
  forall oz: F32
  forall dx: F32
  forall dy: F32
  forall dz: F32
  forall acc: F32
  forall w: F32
  F32

def trace.hit(id, t, dep, ox, oy, oz, dx, dy, dz, acc, w):
  match U32.is_eq(id, 9):
    case False{}:
      match sphere(U32.to_nat(id)):
        case Sph{cx, cy, cz, r, kr}:
          trace.sph(cx, cy, cz, r, kr, t, dep, ox, oy, oz, dx, dy, dz, acc, w)
    case True{}:
      acc

assert trace.sph:
  forall cx: F32
  forall cy: F32
  forall cz: F32
  forall +r: F32
  forall kr: F32
  forall +t: F32
  forall dep: Nat
  forall ox: F32
  forall oy: F32
  forall oz: F32
  forall +dx: F32
  forall +dy: F32
  forall +dz: F32
  forall acc: F32
  forall w: F32
  F32

def trace.sph(cx, cy, cz, r, kr, t, dep, ox, oy, oz, dx, dy, dz, acc, w):
  +hx = F32.add(ox, F32.mul(t, dx))
  +hy = F32.add(oy, F32.mul(t, dy))
  +hz = F32.add(oz, F32.mul(t, dz))
  +nx = F32.div(F32.sub(hx, cx), r)
  +ny = F32.div(F32.sub(hy, cy), r)
  +nz = F32.div(F32.sub(hz, cz), r)
  +lvx = F32.sub(F32.sub(U32.to_f32(0), U32.to_f32(3)), hx)
  +lvy = F32.sub(U32.to_f32(8), hy)
  +lvz = F32.sub(U32.to_f32(1), hz)
  +ll = F32.sqrt(F32.add(F32.add(F32.mul(lvx, lvx), F32.mul(lvy, lvy)), F32.mul(lvz, lvz)))
  +lx = F32.div(lvx, ll)
  +ly = F32.div(lvy, ll)
  +lz = F32.div(lvz, ll)
  df = fmax0(F32.add(F32.add(F32.mul(nx, lx), F32.mul(ny, ly)), F32.mul(nz, lz)))
  +sox = F32.add(hx, F32.mul(fl(1, 1000), nx))
  +soy = F32.add(hy, F32.mul(fl(1, 1000), ny))
  +soz = F32.add(hz, F32.mul(fl(1, 1000), nz))
  trace.lum(nearest(9n, sox, soy, soz, lx, ly, lz, U32.to_f32(1000000000), 9), ll, df, dep, kr, sox, soy, soz, dx, dy, dz, nx, ny, nz, acc, w)

assert trace.lum:
  forall h1: Hit
  forall ll: F32
  forall df: F32
  forall dep: Nat
  forall kr: F32
  forall sox: F32
  forall soy: F32
  forall soz: F32
  forall dx: F32
  forall dy: F32
  forall dz: F32
  forall nx: F32
  forall ny: F32
  forall nz: F32
  forall acc: F32
  forall w: F32
  F32

def trace.lum(h1, ll, df, dep, kr, sox, soy, soz, dx, dy, dz, nx, ny, nz, acc, w):
  match h1:
    case Hit{st, si}:
      trace.dep(dep, F32.add(fl(1, 10), F32.mul(fl(85, 100), shade(st, ll, df))), kr, sox, soy, soz, dx, dy, dz, nx, ny, nz, acc, w)

assert trace.dep:
  forall dep: Nat
  forall lum: F32
  forall kr: F32
  forall sox: F32
  forall soy: F32
  forall soz: F32
  forall +dx: F32
  forall +dy: F32
  forall +dz: F32
  forall +nx: F32
  forall +ny: F32
  forall +nz: F32
  forall acc: F32
  forall w: F32
  F32

def trace.dep(dep, lum, kr, sox, soy, soz, dx, dy, dz, nx, ny, nz, acc, w):
  match dep:
    case 0n:
      F32.add(acc, F32.mul(w, lum))
    case 1n+k:
      trace.rfl(k, F32.mul(U32.to_f32(2), F32.add(F32.add(F32.mul(dx, nx), F32.mul(dy, ny)), F32.mul(dz, nz))), lum, kr, sox, soy, soz, dx, dy, dz, nx, ny, nz, acc, w)

assert trace.rfl:
  forall k: Nat
  forall +k2: F32
  forall lum: F32
  forall +kr: F32
  forall sox: F32
  forall soy: F32
  forall soz: F32
  forall dx: F32
  forall dy: F32
  forall dz: F32
  forall nx: F32
  forall ny: F32
  forall nz: F32
  forall acc: F32
  forall +w: F32
  F32

def trace.rfl(k, k2, lum, kr, sox, soy, soz, dx, dy, dz, nx, ny, nz, acc, w):
  trace(k, sox, soy, soz, F32.sub(dx, F32.mul(k2, nx)), F32.sub(dy, F32.mul(k2, ny)), F32.sub(dz, F32.mul(k2, nz)), F32.add(acc, F32.mul(F32.mul(w, lum), F32.sub(U32.to_f32(1), kr))), F32.mul(w, kr))

assert subray:
  forall +fx: F32
  forall +fy: F32
  F32

def subray(fx, fy):
  +dl = F32.sqrt(F32.add(F32.add(F32.mul(fx, fx), F32.mul(fy, fy)), U32.to_f32(1)))
  trace(4n, U32.to_f32(0), U32.to_f32(0), U32.to_f32(0), F32.div(fx, dl), F32.div(fy, dl), F32.div(U32.to_f32(1), dl), U32.to_f32(0), U32.to_f32(1))

assert pixel:
  forall x: U32
  forall y: U32
  forall +hw: F32
  forall +hh: F32
  U32

def pixel(x, y, hw, hh):
  +xf = U32.to_f32(x)
  +yf = U32.to_f32(y)
  l1 = subray(F32.div(F32.sub(F32.add(xf, fl(1, 4)), hw), hw), F32.div(F32.sub(hh, F32.add(yf, fl(1, 4))), hw))
  l2 = subray(F32.div(F32.sub(F32.add(xf, fl(3, 4)), hw), hw), F32.div(F32.sub(hh, F32.add(yf, fl(1, 4))), hw))
  l3 = subray(F32.div(F32.sub(F32.add(xf, fl(1, 4)), hw), hw), F32.div(F32.sub(hh, F32.add(yf, fl(3, 4))), hw))
  l4 = subray(F32.div(F32.sub(F32.add(xf, fl(3, 4)), hw), hw), F32.div(F32.sub(hh, F32.add(yf, fl(3, 4))), hw))
  F32.to_u32(F32.mul(U32.to_f32(255), clamp01(F32.mul(F32.add(F32.add(l1, l2), F32.add(l3, l4)), fl(1, 4)))))

assert colf.px:
  forall +xx: U32
  forall y: U32
  forall w: U32
  forall hw: F32
  forall hh: F32
  U32

def colf.px(xx, y, w, hw, hh):
  match U32.is_lt(xx, w):
    case False{}:
      0
    case True{}:
      pixel(xx, y, hw, hh)

assert colf:
  forall +d: Nat
  forall +x: U32
  forall +y: U32
  forall +w: U32
  forall +hw: F32
  forall +hh: F32
  U32

def colf(d, x, y, w, hw, hh):
  match d:
    case 0n:
      colf.px(U32.and(U32.mul(x, 2654435761), 16383), y, w, hw, hh)
    case 1n+p:
      Both{a, b} = {Both{colf(p, x, y, w, hw, hh), colf(p, U32.add(x, U32.shln(p, 1)), y, w, hw, hh)} : Par<U32, U32>}
      U32.add(a, b)

assert rowf:
  forall +d: Nat
  forall +y: U32
  forall +m: U32
  forall +w: U32
  forall +hw: F32
  forall +hh: F32
  U32

def rowf(d, y, m, w, hw, hh):
  match d:
    case 0n:
      colf(14n, 0, U32.and(U32.mul(y, 1588635697), m), w, hw, hh)
    case 1n+p:
      Both{a, b} = {Both{rowf(p, y, m, w, hw, hh), rowf(p, U32.add(y, U32.shln(p, 1)), m, w, hw, hh)} : Par<U32, U32>}
      U32.add(a, b)

assert rows:
  Nat

def rows():
  12n

assert width:
  U32

def width():
  6000

# small: rows 6n width 80 expect 402971; big expect 1924309504
assert main:
  IO(Unit)

def main():
  +rr = rows()
  +w = width()
  hw = U32.to_f32(U32.div(w, 2))
  hh = U32.to_f32(U32.div(U32.shln(rr, 1), 2))
  hm = U32.sub(U32.shln(rr, 1), 1)
  IO.print(U32.show(rowf!(rr, 0, hm, w, hw, hh)))
