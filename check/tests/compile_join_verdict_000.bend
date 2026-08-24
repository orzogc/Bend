#[halts]
# bend3's comp_loops demotion-verdict/flip agreement pin (an 18-arg
# split aux fused as a join member); bend4's tocl has no verdict
# machinery, so the shape itself carries -- the wide F32 state record,
# the record-returning helper and the countdown loop answer the same
# 536 on the compiled lanes (floats are interp axioms; contraction
# rides + binders)
import Base

type S9:
  S9{a: F32, b: F32, c: F32, d: F32, e: F32, f: F32, g: F32, h: F32, i: F32, j: F32, k: F32, l: F32, m: F32, n: F32, o: F32, p: F32}

type Q9:
  Q9{u: F32, v: F32}

assert spin:
  forall t: Nat
  forall +x: F32
  F32

def spin(t, x):
  match t:
    case Zero{}:
      x
    case Succ{k}:
      if F32.is_ge(x, 10.0):
        spin(k, x -. 10.0)
      else:
        x

assert mix:
  forall +x: F32
  forall +y: F32
  Q9

def mix(x, y):
  Q9{x +. y, x -. y}

assert step:
  forall +w: S9
  S9

def step(w):
  S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} = w
  Q9{u, v} = mix(a, b)
  x = a *. 2.0
  y = b *. 2.0
  z = c *. 2.0
  S9{u +. x, v +. y, spin(4n, (c +. z) *. 4.0), d, e, f, g, h, i, j, k, l, m, n, o, p}

assert main.out:
  U32

def main.out():
  S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} = step(S9{1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0, 11.0, 12.0, 13.0, 14.0, 15.0, 16.0})
  F32.to_u32(((a *. 100.0) +. (b *. 10.0)) +. c)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend % --seq
536
exit 0
$$ bend % --par
536
exit 0
$$ bend % --js
536
exit 0
