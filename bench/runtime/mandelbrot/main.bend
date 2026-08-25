import Base
# mandelbrot: histogram-equalized escape-time render of the classic
# viewport, ported 1-to-1 from Bend3's par_mandelbrot. 4096x4096
# pixels, signed 8.8 fixed point packed in u32 two's complement. Every
# pixel runs ITERS branchless iterations (z freezes at escape via sel,
# so the instruction stream is uniform); pass 1 forks 2^18 64-pixel
# chunks that bucket escape times into 8 scalar counters and merges the
# histograms pairwise; a CDF pass turns the root histogram into an
# equalization LUT; pass 2 forks one leaf per pixel, recolors its
# recomputed escape time through the LUT and sums position-weighted
# colors. Checksum mixes the LUT and the recolor sum. Knob: ITERS
# (fine). Iteration and depth counters are Nats (no U32 match in
# Bend4).
#
# Sizes (hd, ITERS): small (2n, 7n) expect 887240761 (verified
# against a Bend3 C run on the cluster), big (18n, 51n) expect
# 3101455856 (from the Bend3 header, verified on the cluster in seq,
# par and metal modes).

type Hs:
  Hl{h0: U32, h1: U32, h2: U32, h3: U32, h4: U32, h5: U32, h6: U32, h7: U32}

type Lut:
  Lut{k0: U32, k1: U32, k2: U32, k3: U32, k4: U32, k5: U32, k6: U32, k7: U32}

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

# arithmetic shift right by 8 over two's-complement u32
assert asr8:
  forall +v: +U32
  U32

def asr8(v):
  U32.or(U32.shrn(8n, v), sel(U32.shrn(31n, v), 0, 4278190080))

# ITERS branchless escape-time iterations: z steps while esc == 0 and
# freezes after (sel), it counts the pre-escape iterations
assert mit:
  forall n: Nat
  forall +cr: +U32
  forall +ci: +U32
  forall +zr: +U32
  forall +zi: +U32
  forall esc: U32
  forall it: U32
  U32

def mit(n, cr, ci, zr, zi, esc, it):
  match n:
    case 0n:
      it
    case 1n+p:
      +r2 = {asr8(U32.mul(zr, zr)) : +U32}
      +i2 = {asr8(U32.mul(zi, zi)) : +U32}
      +e2 = {U32.or(esc, b2u(U32.is_gt(U32.add(r2, i2), 1024))) : +U32}
      nzr = U32.add(U32.sub(r2, i2), cr)
      nzi = U32.add(asr8(U32.mul(2, U32.mul(zr, zi))), ci)
      sr = sel(e2, nzr, zr)
      si = sel(e2, nzi, zi)
      mit(p, cr, ci, sr, si, e2, U32.add(it, b2u(U32.is_zero(e2))))

# one pixel: viewport [-2, 1) x [-1.5, 1.5) over the 4096x4096 grid
assert pix:
  forall +id: +U32
  forall tn: Nat
  U32

def pix(id, tn):
  cr = U32.sub(U32.div(U32.mul(U32.and(id, 4095), 768), 4096), 512)
  ci = U32.sub(U32.div(U32.mul(U32.shrn(12n, id), 768), 4096), 384)
  mit(tn, cr, ci, 0, 0, 0, 0)

# escape time -> one of 8 buckets, knob-stable: (it*8)/ITERS clamped
assert bkt:
  forall it: U32
  forall tn: Nat
  U32

def bkt(it, tn):
  +bq = {U32.div(U32.mul(it, 8), U32.from_nat(tn)) : +U32}
  sel(b2u(U32.is_gt(bq, 7)), bq, 7)

# pass-1 leaf: 64 pixels bucketed into 8 scalar counters
assert hchunk:
  forall +j: +Nat
  forall +i: +U32
  forall +tn: +Nat
  forall h0: U32
  forall h1: U32
  forall h2: U32
  forall h3: U32
  forall h4: U32
  forall h5: U32
  forall h6: U32
  forall h7: U32
  Hs

def hchunk(j, i, tn, h0, h1, h2, h3, h4, h5, h6, h7):
  match j:
    case 0n:
      Hl{h0, h1, h2, h3, h4, h5, h6, h7}
    case 1n+p:
      it = pix(U32.add(i, U32.from_nat(p)), tn)
      +bk = {bkt(it, tn) : +U32}
      m0 = b2u(U32.is_eq(bk, 0))
      m1 = b2u(U32.is_eq(bk, 1))
      m2 = b2u(U32.is_eq(bk, 2))
      m3 = b2u(U32.is_eq(bk, 3))
      m4 = b2u(U32.is_eq(bk, 4))
      m5 = b2u(U32.is_eq(bk, 5))
      m6 = b2u(U32.is_eq(bk, 6))
      m7 = b2u(U32.is_eq(bk, 7))
      hchunk(p, i, tn, U32.add(h0, m0), U32.add(h1, m1), U32.add(h2, m2), U32.add(h3, m3), U32.add(h4, m4), U32.add(h5, m5), U32.add(h6, m6), U32.add(h7, m7))

assert hzip:
  forall a: Hs
  forall b: Hs
  Hs

def hzip(a, b):
  match a b:
    case Hl{a0, a1, a2, a3, a4, a5, a6, a7} Hl{b0, b1, b2, b3, b4, b5, b6, b7}:
      Hl{U32.add(a0, b0), U32.add(a1, b1), U32.add(a2, b2), U32.add(a3, b3), U32.add(a4, b4), U32.add(a5, b5), U32.add(a6, b6), U32.add(a7, b7)}

assert hfold:
  forall +d: +Nat
  forall +i: +U32
  forall +tn: +Nat
  Hs

def hfold(d, i, tn):
  match d:
    case 0n:
      hchunk(64n, i, tn, 0, 0, 0, 0, 0, 0, 0, 0)
    case 1n+p:
      a b = hfold(p, i, tn) hfold(p, U32.add(i, U32.shln(p, 64)), tn)
      hzip(a, b)

# histogram equalization: LUT k = cdf(k) scaled to 0..255
assert cdf:
  forall h: Hs
  Lut

def cdf(h):
  match h:
    case Hl{h0, h1, h2, h3, h4, h5, h6, h7}:
      +c0 = {h0 : +U32}
      +c1 = {U32.add(c0, h1) : +U32}
      +c2 = {U32.add(c1, h2) : +U32}
      +c3 = {U32.add(c2, h3) : +U32}
      +c4 = {U32.add(c3, h4) : +U32}
      +c5 = {U32.add(c4, h5) : +U32}
      +c6 = {U32.add(c5, h6) : +U32}
      +c7 = {U32.add(c6, h7) : +U32}
      Lut{U32.div(U32.mul(c0, 255), c7), U32.div(U32.mul(c1, 255), c7), U32.div(U32.mul(c2, 255), c7), U32.div(U32.mul(c3, 255), c7),
          U32.div(U32.mul(c4, 255), c7), U32.div(U32.mul(c5, 255), c7), U32.div(U32.mul(c6, 255), c7), U32.div(U32.mul(c7, 255), c7)}

# pass-2 leaf: recompute the pixel, recolor through the LUT (branchless
# masked pick), weight by a position hash
assert rpix:
  forall +i: +U32
  forall +tn: +Nat
  forall k0: U32
  forall k1: U32
  forall k2: U32
  forall k3: U32
  forall k4: U32
  forall k5: U32
  forall k6: U32
  forall k7: U32
  U32

def rpix(i, tn, k0, k1, k2, k3, k4, k5, k6, k7):
  +it = {pix(i, tn) : +U32}
  +bk = {bkt(it, tn) : +U32}
  col = U32.add(U32.mul(b2u(U32.is_eq(bk, 0)), k0), U32.add(U32.mul(b2u(U32.is_eq(bk, 1)), k1), U32.add(U32.mul(b2u(U32.is_eq(bk, 2)), k2), U32.add(U32.mul(b2u(U32.is_eq(bk, 3)), k3),
        U32.add(U32.mul(b2u(U32.is_eq(bk, 4)), k4), U32.add(U32.mul(b2u(U32.is_eq(bk, 5)), k5), U32.add(U32.mul(b2u(U32.is_eq(bk, 6)), k6), U32.mul(b2u(U32.is_eq(bk, 7)), k7))))))))
  U32.add(U32.mul(col, U32.inc(U32.mul(i, 2654435761))), it)

assert rcol:
  forall +d: +Nat
  forall +i: +U32
  forall +tn: +Nat
  forall +k0: +U32
  forall +k1: +U32
  forall +k2: +U32
  forall +k3: +U32
  forall +k4: +U32
  forall +k5: +U32
  forall +k6: +U32
  forall +k7: +U32
  U32

def rcol(d, i, tn, k0, k1, k2, k3, k4, k5, k6, k7):
  match d:
    case 0n:
      rpix(i, tn, k0, k1, k2, k3, k4, k5, k6, k7)
    case 1n+p:
      a b = rcol(p, i, tn, k0, k1, k2, k3, k4, k5, k6, k7) rcol(p, U32.add(i, U32.shln(p, 1)), tn, k0, k1, k2, k3, k4, k5, k6, k7)
      U32.add(a, b)

assert rend:
  forall +hd: +Nat
  forall +tn: +Nat
  U32

def rend(hd, tn):
  Lut{l0, l1, l2, l3, l4, l5, l6, l7} = cdf(hfold(hd, 0, tn))
  +q0 = {l0 : +U32}
  +q1 = {l1 : +U32}
  +q2 = {l2 : +U32}
  +q3 = {l3 : +U32}
  +q4 = {l4 : +U32}
  +q5 = {l5 : +U32}
  +q6 = {l6 : +U32}
  +q7 = {l7 : +U32}
  m1 = U32.add(U32.mul(q0, 2654435761), q1)
  m2 = U32.add(U32.mul(m1, 2654435761), q2)
  m3 = U32.add(U32.mul(m2, 2654435761), q3)
  m4 = U32.add(U32.mul(m3, 2654435761), q4)
  m5 = U32.add(U32.mul(m4, 2654435761), q5)
  m6 = U32.add(U32.mul(m5, 2654435761), q6)
  m7 = U32.add(U32.mul(m6, 2654435761), q7)
  r = rcol(Nat.add(hd, 6n), 0, tn, q0, q1, q2, q3, q4, q5, q6, q7)
  U32.add(U32.mul(m7, 2654435761), r)

assert its:
  Nat

def its():
  51n

# small: rend!(2n, 7n) expect 887240761; big rend!(18n, its()) expect 3101455856
assert main:
  IO(Unit)

def main():
  IO.print(U32.show(rend!(18n, its())))
