# The runtime stress program: one file that exercises every path of the
# runtime, from the parallel machine down to the collector.
#
# Base supplies the surface: the U32 ops and Array.swap the Rt layer
# adapts are base claims the backends wire straight to the real
# natives. Sharing is spelled with cloned (+) binders, each licensed
# by a Cop witness (base copies for the words, local proved copies for
# Tr and Array<U32>); the C runtime backs each with its RC redirector.
#
# PART ONE - the machine, the closures and the collector. One
# algorithm, three defs. `spawn` builds a depth-20 tree of array
# transformers by fork/join: each of the 1,048,576 leaves is a heap
# closure capturing four U32s, each of the 1,048,575 nodes a
# composition closure capturing its two child closures, so closures are
# stored inside envs and extracted again at application; the two
# recursive calls per node are independent (the parallelism), and each
# node also sums its forks' values (a parallel reduction). The tree
# escapes as one affine value holding 2,097,151 environments. `run.out`
# applies the root once to a fresh 64-slot array: every leaf then fires
# a read-modify-write THROUGH its captured env (~4M native ops), and
# each spent environment feeds the collector. `churn` drains the
# result: per seed character, one native swap at a slot chosen by the
# accumulator, one digit char emitted from what the slot held, one Bool
# branch on that digit, tail call; at SNil the accumulator and the
# whole live array drop (collector again). The output depends on both
# the parallel sum (it seeds the walk) and the array contents (read
# back per char), so any wrong op anywhere changes the printed string.
#
# Literals stress the intros: the seed string and both chars expand to
# full SCon/Chr/U32/Word trees at the checker, 20n/6n to Succ chains;
# at runtime they are native strings, chars and nats. churn compiles to
# a while(true) loop; spawn compiles to a real fork.
#
# PART TWO - sharing and copy-on-write. `build` forks its halves (a
# parallel-let of whole task calls); `tri` shares one heap tree THREE
# ways and consumes each pointer differently (two destructive folds and
# a shallow probe), so redirectors mint, bump, open by shallow copy and
# collapse; `dropper` shares and then drops one pointer (the count
# path); `nest` re-shares a shared tree through a helper (redirector
# bump, no second redirector); `cow` shares an Array, swaps through one
# pointer and reads both (the copy-on-write path). Its answer is
# 23561 = 23441 + 120, byte-stable across 1 and 8 threads (the census
# fail-stops on any lost or doubled owner).

import Base

# Rt: the mocked C runtime's surface, adapted over the natives
# ------------------------------------------------------------

assert Rt.add:
  forall a: U32
  forall b: U32
  U32

def Rt.add(a, b):
  U32.add(a, b)

assert Rt.mul:
  forall a: U32
  forall b: U32
  U32

def Rt.mul(a, b):
  U32.mul(a, b)

assert Rt.divmod:
  forall +a: +U32
  forall +b: +U32
  U32 & U32

def Rt.divmod(a, b):
  (U32.div(a, b), U32.mod(a, b))

assert Rt.eqz:
  forall a: U32
  Bool

def Rt.eqz(a):
  U32.is_zero(a)

assert Rt.alloc:
  forall +n: +Nat
  forall +x: +U32
  Array<U32>

def Rt.alloc(n, x):
  match n:
    case 0n:
      ALeaf{x}
    case 1n+p:
      ANode{Rt.alloc(p, x), Rt.alloc(p, x)}

# read slot i without net effect: swap i in (reading the old value),
# then swap the old value back; the value crosses the seam twice
assert Rt.read.fin:
  forall w: U32
  forall bz: Array<U32> & U32
  Array<U32> & U32

def Rt.read.fin(w, bz):
  (b3, z) = bz
  (b3, w)

assert Rt.read.back:
  forall +i: +U32
  forall bv: Array<U32> & U32
  Array<U32> & U32

def Rt.read.back(i, bv):
  (b2, v) = bv
  +w = {v : +U32}
  Rt.read.fin(w, Array.swap(U32, b2, i, w))

assert Rt.read:
  forall b: Array<U32>
  forall +i: +U32
  Array<U32> & U32

def Rt.read(b, i):
  Rt.read.back(i, Array.swap(U32, b, i, i))

assert Rt.write:
  forall b: Array<U32>
  forall i: U32
  forall v: U32
  Array<U32>

def Rt.write(b, i, v):
  Array.set.fin(Array.swap(U32, b, i, v))

assert Rt.swap:
  forall b: Array<U32>
  forall i: U32
  forall v: U32
  Array<U32> & U32

def Rt.swap(b, i, v):
  Array.swap(U32, b, i, v)

# Parallel closure tree: 2^d leaf transformers, 2^d - 1 compositions.
# A leaf captures {i, s, q} and, only when applied, reads slot
# s mod 48, mixes the read value with its captures, and writes it back:
# an array read-modify-write through a closure environment. A node
# captures its two child closures and composes them; its two forks are
# independent and their values join by add. Left seed s+m, right s*s,
# so every path gets a distinct polynomial of the root seed.
assert spawn.leaf.wr:
  forall +s: +U32
  forall q: U32
  forall +j: +U32
  forall bo: Array<U32> & U32
  Array<U32>

def spawn.leaf.wr(s, q, j, bo):
  (b2, old) = bo
  Rt.write(b2, j, Rt.add(Rt.mul(old, s), q))

assert spawn.leaf.go:
  forall +s: +U32
  forall q: U32
  forall +j: +U32
  forall b: Array<U32>
  Array<U32>

def spawn.leaf.go(s, q, j, b):
  spawn.leaf.wr(s, q, j, Rt.read(b, j))

assert spawn.leaf.mk:
  forall +s: +U32
  forall qi: U32 & U32
  U32 & (Array<U32> -> Array<U32>)

def spawn.leaf.mk(s, qi):
  (q, i) = qi
  +j = {i : +U32}
  (s, b => spawn.leaf.go(s, q, j, b))

assert spawn.node:
  forall l: U32 & (Array<U32> -> Array<U32>)
  forall r: U32 & (Array<U32> -> Array<U32>)
  U32 & (Array<U32> -> Array<U32>)

def spawn.node(l, r):
  (va, fa) = l
  (vb, fb) = r
  (Rt.add(va, vb), b => fb(fa(b)))

assert spawn:
  forall +d: +Nat
  forall +m: +U32
  forall +s: +U32
  U32 & (Array<U32> -> Array<U32>)

def spawn(d, m, s):
  match d:
    case 0n:
      spawn.leaf.mk(s, Rt.divmod(s, m))
    case 1n+p:
      spawn.node(spawn(p, m, Rt.add(s, m)), spawn(p, m, Rt.mul(s, s)))

# String-driven drain: per character, one native swap at slot acc mod
# 48 (z is 48 < 64 slots), one digit char from what the slot held
# (t is 10, z doubles as the '0' offset), one Bool branch on that
# digit steering the next mix, tail call. h drops in the branch that
# skips it (affine); at SNil acc and the whole live array drop.
assert churn.pick:
  forall +z: +U32
  forall c: U32
  forall b2: Array<U32>
  forall +o: +U32
  forall h: U32
  forall +u: +U32
  forall e: Bool
  (Array<U32> & U32) & U32

def churn.pick(z, c, b2, o, h, u, e):
  match e:
    case True{}:
      ((b2, Rt.add(o, c)), Rt.add(z, u))
    case False{}:
      ((b2, Rt.add(Rt.mul(o, c), h)), Rt.add(z, u))

assert churn.mix:
  forall +z: +U32
  forall c: U32
  forall b2: Array<U32>
  forall +o: +U32
  forall hr: U32 & U32
  (Array<U32> & U32) & U32

def churn.mix(z, c, b2, o, hr):
  (h, r) = hr
  +u = {r : +U32}
  churn.pick(z, c, b2, o, h, u, Rt.eqz(u))

assert churn.spin:
  forall +t: +U32
  forall +z: +U32
  forall c: U32
  forall bo: Array<U32> & U32
  (Array<U32> & U32) & U32

def churn.spin(t, z, c, bo):
  (b2, old) = bo
  +o = {old : +U32}
  churn.mix(z, c, b2, o, Rt.divmod(o, t))

assert churn.turn:
  forall +t: +U32
  forall +z: +U32
  forall b: Array<U32>
  forall c: U32
  forall qi: U32 & U32
  (Array<U32> & U32) & U32

def churn.turn(t, z, b, c, qi):
  (q, i) = qi
  churn.spin(t, z, c, Rt.swap(b, i, q))

assert churn.wrap:
  forall out: String
  forall r: (Array<U32> & U32) & U32
  (Array<U32> & U32) & String

def churn.wrap(out, r):
  ((b2, nx), d) = r
  ((b2, nx), SCon{Chr{d}, out})

assert churn.fold:
  forall +t: +U32
  forall +z: +U32
  forall b: Array<U32>
  forall acc: U32
  forall c: U32
  forall out: String
  (Array<U32> & U32) & String

def churn.fold(t, z, b, acc, c, out):
  churn.wrap(out, churn.turn(t, z, b, c, Rt.divmod(acc, z)))

assert churn.go:
  forall s: String
  forall st: (Array<U32> & U32) & String
  forall +t: +U32
  forall +z: +U32
  String

def churn.go(s, st, t, z):
  match s:
    case SNil{}:
      ((b, acc), out) = st
      out
    case SCon{Chr{c}, cs}:
      ((b, acc), out) = st
      churn.go(cs, churn.fold(t, z, b, acc, c, out), t, z)

assert churn:
  forall s: String
  forall +t: +U32
  forall +z: +U32
  forall b: Array<U32>
  forall acc: U32
  forall out: String
  String

def churn(s, t, z, b, acc, out):
  churn.go(s, ((b, acc), out), t, z)

# The match extracts numeric constants: a char literal is the only U32
# literal in source, and Chr must be matched to reach the code. '\n' is
# 10 (the digit base and the tree seed); '0' is 48 (the digit offset,
# the alloc fill, and the slot modulus: 48 < 64 = 2^6n slots, so every
# index is in range). f(...) fires the million leaf envs; v, their
# parallel sum, seeds the drain.
assert run.out:
  String

assert run.seed:
  forall +a: +U32
  forall +c: +U32
  forall vf: U32 & (Array<U32> -> Array<U32>)
  String

def run.seed(a, c, vf):
  (v, f) = vf
  churn("Bend stresses its own runtime!", a, c, f(Rt.alloc(6n, c)), v, "")

assert run.mix:
  forall t: U32
  forall z: U32
  String

def run.mix(t, z):
  +a = {t : +U32}
  +c = {z : +U32}
  run.seed(a, c, spawn(20n, c, a))

assert run.chr:
  forall x: Char
  forall y: Char
  String

def run.chr(x, y):
  match x y:
    case Chr{t} Chr{z}:
      run.mix(t, z)

def run.out():
  run.chr('\n', '0')

type Tr:
  L{v: U32}
  N{a: Tr, b: Tr}

# copy witness for the shared heap tree: never emitted, only licenses +Tr
assert Tr.copy:
  forall t: Tr
  Copy(Tr, t) & Copy(Tr, t)

assert Tr.copy.leaf:
  forall -v: U32
  forall c: Copy(U32, v) & Copy(U32, v)
  Copy(Tr, L{v}) & Copy(Tr, L{v})

def Tr.copy.leaf(v, c):
  ((v1, e1), (v2, e2)) = c
  p1 = Equal.cong(U32, Tr, x => L{x}, v, v1, e1)
  p2 = Equal.cong(U32, Tr, x => L{x}, v, v2, e2)
  ((L{v1}, p1), (L{v2}, p2))

assert Tr.copy.node:
  forall -a: Tr
  forall -b: Tr
  forall ca: Copy(Tr, a) & Copy(Tr, a)
  forall cb: Copy(Tr, b) & Copy(Tr, b)
  Copy(Tr, N{a, b}) & Copy(Tr, N{a, b})

def Tr.copy.node(a, b, ca, cb):
  ((a1, ea1), (a2, ea2)) = ca
  ((b1, eb1), (b2, eb2)) = cb
  p1 = Equal.trans(Tr, N{a, b}, N{a1, b}, N{a1, b1},
                   Equal.cong(Tr, Tr, x => N{x, b}, a, a1, ea1),
                   Equal.cong(Tr, Tr, x => N{a1, x}, b, b1, eb1))
  p2 = Equal.trans(Tr, N{a, b}, N{a2, b}, N{a2, b2},
                   Equal.cong(Tr, Tr, x => N{x, b}, a, a2, ea2),
                   Equal.cong(Tr, Tr, x => N{a2, x}, b, b2, eb2))
  ((N{a1, b1}, p1), (N{a2, b2}, p2))

def Tr.copy(t):
  match t:
    case L{v}:
      Tr.copy.leaf(v, U32.copy(v))
    case N{a, b}:
      Tr.copy.node(a, b, Tr.copy(a), Tr.copy(b))

assert build:
  forall +d: +Nat
  forall +x: +U32
  Tr

def build(d, x):
  match d:
    case 0n:
      L{x}
    case 1n+p:
      & a : Tr = build(p, U32.mul(x, 2)) & b : Tr = build(p, U32.add(U32.mul(x, 2), 1));
      N{a, b}

assert sum:
  forall t: Tr
  U32

def sum(t):
  match t:
    case L{v}:
      v
    case N{a, b}:
      & x : U32 = sum(a) & y : U32 = sum(b);
      U32.add(x, y)

assert depth.max:
  forall g: Bool
  U32

def depth.max(g):
  match g:
    case True{}:
      1
    case False{}:
      1

assert depth:
  forall t: Tr
  U32

def depth(t):
  match t:
    case L{v}:
      0
    case N{a, b}:
      depth.max(U32.is_gt(depth(a), depth(b)))

assert tri:
  forall +t: +Tr
  U32

def tri(t):
  U32.add(sum(t), U32.add(sum(t), depth(t)))

assert dropper:
  forall +t: +Tr
  U32

def dropper(t):
  x = sum(t)
  y = t
  x

assert helper:
  forall +u: +Tr
  U32

def helper(u):
  U32.add(sum(u), sum(u))

assert nest:
  forall +t: +Tr
  U32

def nest(t):
  U32.add(helper(t), helper(t))

assert mk:
  Array<U32>

def mk():
  ANode{ANode{ALeaf{1}, ALeaf{2}}, ANode{ALeaf{3}, ALeaf{4}}}

assert rd:
  forall a: Array<U32>
  U32

def rd(a):
  match a:
    case ALeaf{x}:
      x
    case ANode{xs, ys}:
      U32.add(rd(xs), rd(ys))

# proved copy witness over Array<U32> (base's Array.copy is proof-free,
# so +Array<U32> cannot resolve to it); spelled explicitly at cow
assert Arr.copy:
  forall a: Array<U32>
  Copy(Array<U32>, a) & Copy(Array<U32>, a)

assert Arr.copy.leaf:
  forall -v: U32
  forall c: Copy(U32, v) & Copy(U32, v)
  Copy(Array<U32>, ALeaf{v}) & Copy(Array<U32>, ALeaf{v})

def Arr.copy.leaf(v, c):
  ((v1, e1), (v2, e2)) = c
  p1 = Equal.cong(U32, Array<U32>, x => ALeaf{x}, v, v1, e1)
  p2 = Equal.cong(U32, Array<U32>, x => ALeaf{x}, v, v2, e2)
  ((ALeaf{v1}, p1), (ALeaf{v2}, p2))

assert Arr.copy.node:
  forall -xs: Array<U32>
  forall -ys: Array<U32>
  forall cx: Copy(Array<U32>, xs) & Copy(Array<U32>, xs)
  forall cy: Copy(Array<U32>, ys) & Copy(Array<U32>, ys)
  Copy(Array<U32>, ANode{xs, ys}) & Copy(Array<U32>, ANode{xs, ys})

def Arr.copy.node(xs, ys, cx, cy):
  ((x1, ex1), (x2, ex2)) = cx
  ((y1, ey1), (y2, ey2)) = cy
  p1 = Equal.trans(Array<U32>, ANode{xs, ys}, ANode{x1, ys}, ANode{x1, y1},
                   Equal.cong(Array<U32>, Array<U32>, x => ANode{x, ys}, xs, x1, ex1),
                   Equal.cong(Array<U32>, Array<U32>, x => ANode{x1, x}, ys, y1, ey1))
  p2 = Equal.trans(Array<U32>, ANode{xs, ys}, ANode{x2, ys}, ANode{x2, y2},
                   Equal.cong(Array<U32>, Array<U32>, x => ANode{x, ys}, xs, x2, ex2),
                   Equal.cong(Array<U32>, Array<U32>, x => ANode{x2, x}, ys, y2, ey2))
  ((ANode{x1, y1}, p1), (ANode{x2, y2}, p2))

def Arr.copy(a):
  match a:
    case ALeaf{v}:
      Arr.copy.leaf(v, U32.copy(v))
    case ANode{xs, ys}:
      Arr.copy.node(xs, ys, Arr.copy(xs), Arr.copy(ys))

assert cow.fin:
  forall +a: +Array<U32> ~ Arr.copy
  forall bo: Array<U32> & U32
  U32

def cow.fin(a, bo):
  (b, old) = bo
  U32.add(rd(b), U32.add(rd(a), old))

assert cow:
  forall +a: +Array<U32> ~ Arr.copy
  U32

def cow(a):
  cow.fin(a, Array.swap(U32, a, 0, 100))

assert share.out:
  U32

def share.out():
  p = tri(build(6n, 1))
  q = dropper(build(5n, 3))
  r = nest(build(4n, 7))
  U32.add(U32.add(p, U32.add(q, r)), cow(mk()))

assert main:
  IO(Unit)

def main():
  do IO<Unit>:
    u : Unit <- IO.print(run.out())
    IO.print(U32.show(share.out()))
