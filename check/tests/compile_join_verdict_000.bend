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

# copy witness for the wide record: never emitted, only licenses +S9
# (a rewrite ladder replaces the 16-field cong/trans chain)
assert S9.copy:
  forall w: S9
  Copy(S9, w) & Copy(S9, w)

def S9.copy(w):
  match w:
    case S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p}:
      ((a1, qa1), (a2, qa2)) = F32.copy(a)
      ((b1, qb1), (b2, qb2)) = F32.copy(b)
      ((c1, qc1), (c2, qc2)) = F32.copy(c)
      ((d1, qd1), (d2, qd2)) = F32.copy(d)
      ((e1, qe1), (e2, qe2)) = F32.copy(e)
      ((f1, qf1), (f2, qf2)) = F32.copy(f)
      ((g1, qg1), (g2, qg2)) = F32.copy(g)
      ((h1, qh1), (h2, qh2)) = F32.copy(h)
      ((i1, qi1), (i2, qi2)) = F32.copy(i)
      ((j1, qj1), (j2, qj2)) = F32.copy(j)
      ((k1, qk1), (k2, qk2)) = F32.copy(k)
      ((l1, ql1), (l2, ql2)) = F32.copy(l)
      ((m1, qm1), (m2, qm2)) = F32.copy(m)
      ((n1, qn1), (n2, qn2)) = F32.copy(n)
      ((o1, qo1), (o2, qo2)) = F32.copy(o)
      ((p1, qp1), (p2, qp2)) = F32.copy(p)
      ((S9{a1, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1},
            %qa1 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{_, b1, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1} : S9};
            %qb1 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, _, c1, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1} : S9};
            %qc1 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, _, d1, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1} : S9};
            %qd1 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, _, e1, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1} : S9};
            %qe1 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, _, f1, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1} : S9};
            %qf1 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, e, _, g1, h1, i1, j1, k1, l1, m1, n1, o1, p1} : S9};
            %qg1 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, e, f, _, h1, i1, j1, k1, l1, m1, n1, o1, p1} : S9};
            %qh1 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, e, f, g, _, i1, j1, k1, l1, m1, n1, o1, p1} : S9};
            %qi1 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, e, f, g, h, _, j1, k1, l1, m1, n1, o1, p1} : S9};
            %qj1 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, e, f, g, h, i, _, k1, l1, m1, n1, o1, p1} : S9};
            %qk1 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, e, f, g, h, i, j, _, l1, m1, n1, o1, p1} : S9};
            %ql1 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, e, f, g, h, i, j, k, _, m1, n1, o1, p1} : S9};
            %qm1 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, e, f, g, h, i, j, k, l, _, n1, o1, p1} : S9};
            %qn1 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, e, f, g, h, i, j, k, l, m, _, o1, p1} : S9};
            %qo1 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, _, p1} : S9};
            %qp1 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, _} : S9};
            {==}),
       (S9{a2, b2, c2, d2, e2, f2, g2, h2, i2, j2, k2, l2, m2, n2, o2, p2},
            %qa2 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{_, b2, c2, d2, e2, f2, g2, h2, i2, j2, k2, l2, m2, n2, o2, p2} : S9};
            %qb2 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, _, c2, d2, e2, f2, g2, h2, i2, j2, k2, l2, m2, n2, o2, p2} : S9};
            %qc2 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, _, d2, e2, f2, g2, h2, i2, j2, k2, l2, m2, n2, o2, p2} : S9};
            %qd2 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, _, e2, f2, g2, h2, i2, j2, k2, l2, m2, n2, o2, p2} : S9};
            %qe2 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, _, f2, g2, h2, i2, j2, k2, l2, m2, n2, o2, p2} : S9};
            %qf2 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, e, _, g2, h2, i2, j2, k2, l2, m2, n2, o2, p2} : S9};
            %qg2 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, e, f, _, h2, i2, j2, k2, l2, m2, n2, o2, p2} : S9};
            %qh2 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, e, f, g, _, i2, j2, k2, l2, m2, n2, o2, p2} : S9};
            %qi2 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, e, f, g, h, _, j2, k2, l2, m2, n2, o2, p2} : S9};
            %qj2 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, e, f, g, h, i, _, k2, l2, m2, n2, o2, p2} : S9};
            %qk2 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, e, f, g, h, i, j, _, l2, m2, n2, o2, p2} : S9};
            %ql2 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, e, f, g, h, i, j, k, _, m2, n2, o2, p2} : S9};
            %qm2 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, e, f, g, h, i, j, k, l, _, n2, o2, p2} : S9};
            %qn2 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, e, f, g, h, i, j, k, l, m, _, o2, p2} : S9};
            %qo2 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, _, p2} : S9};
            %qp2 : {S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p} == S9{a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, _} : S9};
            {==}))

assert spin:
  forall t: Nat
  forall +x: +F32
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
  forall +x: +F32
  forall +y: +F32
  Q9

def mix(x, y):
  Q9{x +. y, x -. y}

assert step:
  forall +w: +S9
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
