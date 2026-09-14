import Base
# Symreg: symbolic regression over expression-tree ADTs, ported 1-to-1
# from Bend3's par_symreg. A population of 2^SIZE candidate programs
# (each a depth-5 arithmetic AST -- add/sub/mul/xor internals,
# x/literal leaves -- materialized from a xorshift32 stream) hunts
# f(x) = x*x + 3x + 7 over the dataset x = 0..PTS-1. Per candidate:
# gen builds the tree, floop folds the dataset through eval (a
# pattern-matching interpreter reading the tree through a shared +e
# arg), and the fitness adds a parsimony penalty of 8 per AST node
# (esize). batch forks the population as a balanced tree; pick runs
# the tournament pairwise up the forks, keeping the (fit, seed) winner
# and summing per-candidate checksums. climb then hill-climbs the
# winner for 32 sequential mutation rounds. Result mixes the climbed
# winner with the population checksum. Per-node ctor pattern-matching:
# the pattern-match-bottlenecked bench of the suite. Depth, dataset
# and round counters are Nats (no U32 match in Bend4); node dispatches
# on a Nat opcode.
#
# Sizes (size, pts): small (6, 16) expect 2490246820 (verified against
# a Bend3 C run on the cluster), big (18, 110) expect 2383953211 (from
# the Bend3 header).

type Expr is Data:
  Var{}
  Lit{v: U32}
  Add{a: Expr, b: Expr}
  Sub{a: Expr, b: Expr}
  Mul{a: Expr, b: Expr}
  Xor{a: Expr, b: Expr}

type Sel is Data:
  Sel{fit: U32, seed: U32, sum: U32}

law Sel.fit:
  for v: Sel
  U32

def Sel.fit(v):
  match v:
    case Sel{f, s, c}:
      f

law Sel.seed:
  for v: Sel
  U32

def Sel.seed(v):
  match v:
    case Sel{f, s, c}:
      s

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

law sel.go:
  for x: U32
  for y: U32
  for z: Bool
  U32

def sel.go(x, y, z):
  match z:
    case True{}:
      x
    case False{}:
      y

law sel:
  for t: U32
  for x: U32
  for y: U32
  U32

def sel(t, x, y):
  sel.go(x, y, U32.is_zero(t))

law adiff:
  for +a: U32
  for +b: U32
  U32

def adiff(a, b):
  sel(b2u(U32.is_lt(a, b)), U32.sub(a, b), U32.sub(b, a))

law node:
  for o: Nat
  for a: Expr
  for b: Expr
  Expr

def node(o, a, b):
  match o:
    case 0n:
      Add{a, b}
    case 1n:
      Sub{a, b}
    case 2n:
      Mul{a, b}
    case 3n+p:
      Xor{a, b}

# materialize a candidate AST straight off the hash stream
law gen.leaf:
  for +h: U32
  for z: Bool
  Expr

law gen:
  for +d: Nat
  for +h: U32
  Expr

def gen.leaf(h, z):
  match z:
    case True{}:
      Var{}
    case False{}:
      Lit{U32.and(h, 255)}

def gen(d, h):
  match d:
    case 0n:
      gen.leaf(h, U32.is_zero(U32.and(U32.shrn(h, 8n), 1)))
    case 1n+p:
      a = gen(p, prng(U32.xor(h, 2654435761)))
      b = gen(p, prng(U32.add(h, 340573321)))
      node(U32.to_nat(U32.mod(h, 4)), a, b)

# pattern-matching interpreter reading the shared tree
law eval:
  for e: Expr
  for +x: U32
  U32

def eval(e, x):
  match e:
    case Var{}:
      x
    case Lit{v}:
      v
    case Add{a, b}:
      U32.add(eval(a, x), eval(b, x))
    case Sub{a, b}:
      U32.sub(eval(a, x), eval(b, x))
    case Mul{a, b}:
      U32.mul(eval(a, x), eval(b, x))
    case Xor{a, b}:
      U32.xor(eval(a, x), eval(b, x))

# parsimony: AST node count off the shared tree
law esize:
  for e: Expr
  U32

def esize(e):
  match e:
    case Var{}:
      1
    case Lit{v}:
      1
    case Add{a, b}:
      U32.add(1, U32.add(esize(a), esize(b)))
    case Sub{a, b}:
      U32.add(1, U32.add(esize(a), esize(b)))
    case Mul{a, b}:
      U32.add(1, U32.add(esize(a), esize(b)))
    case Xor{a, b}:
      U32.add(1, U32.add(esize(a), esize(b)))

# dataset fold: error sum over x = 0..j-1, then the parsimony penalty
law floop:
  for +j: Nat
  for +e: Expr
  for acc: U32
  U32

def floop(j, e, acc):
  match j:
    case 0n:
      U32.add(acc, U32.mul(esize(e), 8))
    case 1n+p:
      +xx = U32.from_nat(p)
      v = eval(e, xx)
      t = U32.add(U32.mul(xx, xx), U32.add(U32.mul(3, xx), 7))
      floop(p, e, U32.add(acc, adiff(v, t)))

law cand:
  for +s: U32
  for pts: Nat
  Sel

def cand(s, pts):
  t = gen(5n, prng(s))
  +f = floop(pts, t, 0)
  Sel{f, s, U32.xor(f, U32.mul(s, 2654435761))}

# tournament: keep the lower-fitness candidate, sum the checksums
law pick:
  for a: Sel
  for b: Sel
  Sel

def pick(a, b):
  match a b:
    case Sel{+f1, s1, c1} Sel{+f2, s2, c2}:
      +w = b2u(U32.is_lt(f1, f2))
      Sel{sel(w, f2, f1), sel(w, s2, s1), U32.add(c1, c2)}

law batch:
  for +d: Nat
  for +s: U32
  for +pts: Nat
  Sel

def batch(d, s, pts):
  match d:
    case 0n:
      cand(prng(s), pts)
    case 1n+p:
      a b = batch(p, U32.add(U32.mul(s, 1664525), 1), pts) batch(p, U32.add(U32.mul(s, 214013), 3), pts)
      pick(a, b)

# hill-climb the tournament winner: mutate the seed, keep improvements
law climb:
  for +r: Nat
  for +bs: U32
  for +bf: U32
  for +pts: Nat
  U32

def climb(r, bs, bf, pts):
  match r:
    case 0n:
      U32.xor(bf, U32.mul(bs, 2654435761))
    case 1n+p:
      +cn = cand(prng(U32.xor(bs, U32.mul(U32.inc(U32.from_nat(p)), 40503))), pts)
      +ff = Sel.fit(cn)
      +w = b2u(U32.is_lt(ff, bf))
      climb(p, sel(w, bs, Sel.seed(cn)), sel(w, bf, ff), pts)

law run.fin:
  for r: Nat
  for +p: Nat
  for t: Sel
  U32

law run:
  for d: Nat
  for s0: U32
  for r: Nat
  for +p: Nat
  U32

def run.fin(r, p, t):
  match t:
    case Sel{f, s, c}:
      U32.add(climb(r, s, f, p), c)

def run(d, s0, r, p):
  run.fin(r, p, batch(d, s0, p))

law size:
  Nat

def size():
  18n

law pts:
  Nat

def pts():
  110n

# small: run!(6n, 42, 32n, 16n) expect 2490246820; big expect 2383953211
law main:
  IO(Unit)

def main():
  IO.print(U32.show(run!(size(), 42, 32n, pts())))
