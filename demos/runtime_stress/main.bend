# The runtime stress program: one file that exercises every path of the
# runtime, from the parallel machine down to the collector.
#
# Base supplies the surface: the U32 ops and Array.swap the Rt layer
# adapts are base claims the backends wire straight to the real
# natives. Sharing is spelled with + binders over Data types (the
# words and the Tr tree); the C runtime backs each with its RC
# redirector. An Array is affine: cow duplicates it with Array.clone.
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
# bump, no second redirector); `cow` clones an Array, swaps through one
# copy and reads both. Its answer is
# 23561 = 23441 + 120, byte-stable across 1 and 8 threads (the census
# fail-stops on any lost or doubled owner).

import Base

# Rt: the mocked C runtime's surface, adapted over the natives
# ------------------------------------------------------------

law Rt.add:
  for a: U32
  for b: U32
  U32

def Rt.add(a, b):
  U32.add(a, b)

law Rt.mul:
  for a: U32
  for b: U32
  U32

def Rt.mul(a, b):
  U32.mul(a, b)

law Rt.divmod:
  for +a: U32
  for +b: U32
  U32 & U32

def Rt.divmod(a, b):
  (U32.div(a, b), U32.mod(a, b))

law Rt.eqz:
  for a: U32
  Bool

def Rt.eqz(a):
  U32.is_zero(a)

law Rt.alloc:
  for +n: Nat
  for +x: U32
  Array<U32>

def Rt.alloc(n, x):
  match n:
    case 0n:
      ALeaf{x}
    case 1n+p:
      ANode{Rt.alloc(p, x), Rt.alloc(p, x)}

# read slot i without net effect: swap i in (reading the old value),
# then swap the old value back; the value crosses the seam twice
law Rt.read.fin:
  for val : U32
  for bz  : Array<U32> & U32
  Array<U32> & U32

def Rt.read.fin(val, bz):
  (b3, z) = bz
  (b3, val)

law Rt.read.back:
  for +i : U32
  for bv : Array<U32> & U32
  Array<U32> & U32

def Rt.read.back(i, bv):
  (b2, v) = bv
  +val = v
  Rt.read.fin(val, Array.swap(U32, b2, i, val))

law Rt.read:
  for  b: Array<U32>
  for +i: U32
  Array<U32> & U32

def Rt.read(b, i):
  Rt.read.back(i, Array.swap(U32, b, i, i))

law Rt.write:
  for b: Array<U32>
  for i: U32
  for v: U32
  Array<U32>

def Rt.write(b, i, v):
  Array.set.fin(U32, Array.swap(U32, b, i, v))

law Rt.swap:
  for b: Array<U32>
  for i: U32
  for v: U32
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
law spawn.leaf.wr:
  for +s : U32
  for q  : U32
  for +j : U32
  for bo : Array<U32> & U32
  Array<U32>

def spawn.leaf.wr(s, q, j, bo):
  (b2, old) = bo
  Rt.write(b2, j, Rt.add(Rt.mul(old, s), q))

law spawn.leaf.go:
  for +s: U32
  for  q: U32
  for +j: U32
  for  b: Array<U32>
  Array<U32>

def spawn.leaf.go(s, q, j, b):
  spawn.leaf.wr(s, q, j, Rt.read(b, j))

law spawn.leaf.mk:
  for +s : U32
  for qi : U32 & U32
  U32 & (Array<U32> -> Array<U32>)

def spawn.leaf.mk(s, qi):
  (q, i) = qi
  +j = i
  (s, b => spawn.leaf.go(s, q, j, b))

law spawn.node:
  for l: U32 & (Array<U32> -> Array<U32>)
  for r: U32 & (Array<U32> -> Array<U32>)
  U32 & (Array<U32> -> Array<U32>)

def spawn.node(l, r):
  (va, fa) = l
  (vb, fb) = r
  (Rt.add(va, vb), b => fb(fa(b)))

law spawn:
  for +d: Nat
  for +m: U32
  for +s: U32
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
# digit steering the next mix, tail call. quo drops in the branch that
# skips it (affine); at SNil acc and the whole live array drop.
law churn.pick:
  for +z   : U32
  for c    : U32
  for b2   : Array<U32>
  for +o   : U32
  for quo  : U32
  for +dig : U32
  for is0  : Bool
  (Array<U32> & U32) & U32

def churn.pick(z, c, b2, o, quo, dig, is0):
  match is0:
    case True{}:
      ((b2, Rt.add(o, c)), Rt.add(z, dig))
    case False{}:
      ((b2, Rt.add(Rt.mul(o, c), quo)), Rt.add(z, dig))

law churn.mix:
  for +z : U32
  for c  : U32
  for b2 : Array<U32>
  for +o : U32
  for qr : U32 & U32
  (Array<U32> & U32) & U32

def churn.mix(z, c, b2, o, qr):
  (quo, r) = qr
  +dig = r
  churn.pick(z, c, b2, o, quo, dig, Rt.eqz(dig))

law churn.spin:
  for +t : U32
  for +z : U32
  for c  : U32
  for bo : Array<U32> & U32
  (Array<U32> & U32) & U32

def churn.spin(t, z, c, bo):
  (b2, old) = bo
  +o = old
  churn.mix(z, c, b2, o, Rt.divmod(o, t))

law churn.turn:
  for +t : U32
  for +z : U32
  for b  : Array<U32>
  for c  : U32
  for qi : U32 & U32
  (Array<U32> & U32) & U32

def churn.turn(t, z, b, c, qi):
  (q, i) = qi
  churn.spin(t, z, c, Rt.swap(b, i, q))

law churn.wrap:
  for out : String
  for r   : (Array<U32> & U32) & U32
  (Array<U32> & U32) & String

def churn.wrap(out, r):
  ((b2, nx), ch) = r
  ((b2, nx), SCon{Chr{ch}, out})

law churn.fold:
  for +t  : U32
  for +z  : U32
  for b   : Array<U32>
  for acc : U32
  for c   : U32
  for out : String
  (Array<U32> & U32) & String

def churn.fold(t, z, b, acc, c, out):
  churn.wrap(out, churn.turn(t, z, b, c, Rt.divmod(acc, z)))

law churn.go:
  for s  : String
  for st : (Array<U32> & U32) & String
  for +t : U32
  for +z : U32
  String

def churn.go(s, st, t, z):
  match s:
    case SNil{}:
      ((b, acc), out) = st
      out
    case SCon{Chr{c}, cs}:
      ((b, acc), out) = st
      churn.go(cs, churn.fold(t, z, b, acc, c, out), t, z)

law churn:
  for s   : String
  for +t  : U32
  for +z  : U32
  for b   : Array<U32>
  for acc : U32
  for out : String
  String

def churn(s, t, z, b, acc, out):
  churn.go(s, ((b, acc), out), t, z)

# The match extracts numeric constants: a char literal is the only U32
# literal in source, and Chr must be matched to reach the code. '\n' is
# 10 (the digit base and the tree seed); '0' is 48 (the digit offset,
# the alloc fill, and the slot modulus: 48 < 64 = 2^6n slots, so every
# index is in range). f(...) fires the million leaf envs; v, their
# parallel sum, seeds the drain.
law run.out:
  String

law run.seed:
  for +ten : U32
  for +off : U32
  for vf   : U32 & (Array<U32> -> Array<U32>)
  String

def run.seed(ten, off, vf):
  (v, f) = vf
  churn("Bend stresses its own runtime!", ten, off, f(Rt.alloc(6n, off)), v, "")

law run.mix:
  for t: U32
  for z: U32
  String

def run.mix(t, z):
  +ten = t
  +off = z
  run.seed(ten, off, spawn(20n, off, ten))

law run.chr:
  for x: Char
  for y: Char
  String

def run.chr(x, y):
  match x y:
    case Chr{t} Chr{z}:
      run.mix(t, z)

def run.out():
  run.chr('\n', '0')

type Tr is Data:
  L{v: U32}
  N{a: Tr, b: Tr}

law build:
  for +d: Nat
  for +x: U32
  Tr

def build(d, x):
  match d:
    case 0n:
      L{x}
    case 1n+p:
      a b = build(p, U32.mul(x, 2)) build(p, U32.add(U32.mul(x, 2), 1))
      N{a, b}

law sum:
  for t: Tr
  U32

def sum(t):
  match t:
    case L{v}:
      v
    case N{a, b}:
      x y = sum(a) sum(b)
      U32.add(x, y)

law depth.max:
  for g: Bool
  U32

def depth.max(g):
  match g:
    case True{}:
      1
    case False{}:
      1

law depth:
  for t: Tr
  U32

def depth(t):
  match t:
    case L{v}:
      0
    case N{a, b}:
      depth.max(U32.is_gt(depth(a), depth(b)))

law tri:
  for +t: Tr
  U32

def tri(t):
  U32.add(sum(t), U32.add(sum(t), depth(t)))

law dropper:
  for +t: Tr
  U32

def dropper(t):
  x = sum(t)
  y = t
  x

law helper:
  for +u: Tr
  U32

def helper(u):
  U32.add(sum(u), sum(u))

law nest:
  for +t: Tr
  U32

def nest(t):
  U32.add(helper(t), helper(t))

law mk:
  Array<U32>

def mk():
  ANode{ANode{ALeaf{1}, ALeaf{2}}, ANode{ALeaf{3}, ALeaf{4}}}

law rd:
  for a: Array<U32>
  U32

def rd(a):
  match a:
    case ALeaf{x}:
      x
    case ANode{xs, ys}:
      U32.add(rd(xs), rd(ys))

law cow.fin:
  for a  : Array<U32>
  for bo : Array<U32> & U32
  U32

def cow.fin(a, bo):
  (b, old) = bo
  U32.add(rd(b), U32.add(rd(a), old))

law cow.go:
  for aa: Array<U32> & Array<U32>
  U32

def cow.go(aa):
  (a, a2) = aa
  cow.fin(a, Array.swap(U32, a2, 0, 100))

law cow:
  for a: Array<U32>
  U32

def cow(a):
  cow.go(Array.clone(a))

law share.out:
  U32

def share.out():
  p = tri(build(6n, 1))
  q = dropper(build(5n, 3))
  r = nest(build(4n, 7))
  U32.add(U32.add(p, U32.add(q, r)), cow(mk()))

law main:
  IO(Unit)

def main():
  do IO<Unit>:
    u : Unit <- IO.print(run.out())
    IO.print(U32.show(share.out()))
