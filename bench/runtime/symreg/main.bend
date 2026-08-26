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

type Expr:
  Var{}
  Lit{v: U32}
  Add{a: Expr, b: Expr}
  Sub{a: Expr, b: Expr}
  Mul{a: Expr, b: Expr}
  Xor{a: Expr, b: Expr}

type Sel:
  Sel{fit: U32, seed: U32, sum: U32}

assert Sel.copy.go:
  forall -f: U32
  forall -s: U32
  forall -c: U32
  forall cf: Copy(U32, f) & Copy(U32, f)
  forall cs: Copy(U32, s) & Copy(U32, s)
  forall cc: Copy(U32, c) & Copy(U32, c)
  Copy(Sel, Sel{f, s, c}) & Copy(Sel, Sel{f, s, c})

def Sel.copy.go(f, s, c, cf, cs, cc):
  ((f1, e1), (f2, e2)) = cf
  ((s1, g1), (s2, g2)) = cs
  ((c1, h1), (c2, h2)) = cc
  p1 = Equal.trans(Sel, Sel{f, s, c}, Sel{f1, s, c}, Sel{f1, s1, c1},
                   Equal.cong(U32, Sel, x => Sel{x, s, c}, f, f1, e1),
                   Equal.trans(Sel, Sel{f1, s, c}, Sel{f1, s1, c}, Sel{f1, s1, c1},
                               Equal.cong(U32, Sel, x => Sel{f1, x, c}, s, s1, g1),
                               Equal.cong(U32, Sel, x => Sel{f1, s1, x}, c, c1, h1)))
  p2 = Equal.trans(Sel, Sel{f, s, c}, Sel{f2, s, c}, Sel{f2, s2, c2},
                   Equal.cong(U32, Sel, x => Sel{x, s, c}, f, f2, e2),
                   Equal.trans(Sel, Sel{f2, s, c}, Sel{f2, s2, c}, Sel{f2, s2, c2},
                               Equal.cong(U32, Sel, x => Sel{f2, x, c}, s, s2, g2),
                               Equal.cong(U32, Sel, x => Sel{f2, s2, x}, c, c2, h2)))
  ((Sel{f1, s1, c1}, p1), (Sel{f2, s2, c2}, p2))

assert Sel.copy:
  forall v: Sel
  Copy(Sel, v) & Copy(Sel, v)

def Sel.copy(v):
  match v:
    case Sel{f, s, c}:
      Sel.copy.go(f, s, c, U32.copy(f), U32.copy(s), U32.copy(c))

assert Sel.fit:
  forall v: Sel
  U32

def Sel.fit(v):
  match v:
    case Sel{f, s, c}:
      f

assert Sel.seed:
  forall v: Sel
  U32

def Sel.seed(v):
  match v:
    case Sel{f, s, c}:
      s

# copy witness for the shared tree: never emitted, only licenses +Expr
assert Expr.copy.lit:
  forall -v: U32
  forall cv: Copy(U32, v) & Copy(U32, v)
  Copy(Expr, Lit{v}) & Copy(Expr, Lit{v})

def Expr.copy.lit(v, cv):
  ((v1, e1), (v2, e2)) = cv
  p1 = Equal.cong(U32, Expr, x => Lit{x}, v, v1, e1)
  p2 = Equal.cong(U32, Expr, x => Lit{x}, v, v2, e2)
  ((Lit{v1}, p1), (Lit{v2}, p2))

assert Expr.copy.add:
  forall -a: Expr
  forall -b: Expr
  forall ca: Copy(Expr, a) & Copy(Expr, a)
  forall cb: Copy(Expr, b) & Copy(Expr, b)
  Copy(Expr, Add{a, b}) & Copy(Expr, Add{a, b})

def Expr.copy.add(a, b, ca, cb):
  ((a1, ea1), (a2, ea2)) = ca
  ((b1, eb1), (b2, eb2)) = cb
  p1 = Equal.trans(Expr, Add{a, b}, Add{a1, b}, Add{a1, b1}, Equal.cong(Expr, Expr, x => Add{x, b}, a, a1, ea1), Equal.cong(Expr, Expr, x => Add{a1, x}, b, b1, eb1))
  p2 = Equal.trans(Expr, Add{a, b}, Add{a2, b}, Add{a2, b2}, Equal.cong(Expr, Expr, x => Add{x, b}, a, a2, ea2), Equal.cong(Expr, Expr, x => Add{a2, x}, b, b2, eb2))
  ((Add{a1, b1}, p1), (Add{a2, b2}, p2))

assert Expr.copy.sub:
  forall -a: Expr
  forall -b: Expr
  forall ca: Copy(Expr, a) & Copy(Expr, a)
  forall cb: Copy(Expr, b) & Copy(Expr, b)
  Copy(Expr, Sub{a, b}) & Copy(Expr, Sub{a, b})

def Expr.copy.sub(a, b, ca, cb):
  ((a1, ea1), (a2, ea2)) = ca
  ((b1, eb1), (b2, eb2)) = cb
  p1 = Equal.trans(Expr, Sub{a, b}, Sub{a1, b}, Sub{a1, b1}, Equal.cong(Expr, Expr, x => Sub{x, b}, a, a1, ea1), Equal.cong(Expr, Expr, x => Sub{a1, x}, b, b1, eb1))
  p2 = Equal.trans(Expr, Sub{a, b}, Sub{a2, b}, Sub{a2, b2}, Equal.cong(Expr, Expr, x => Sub{x, b}, a, a2, ea2), Equal.cong(Expr, Expr, x => Sub{a2, x}, b, b2, eb2))
  ((Sub{a1, b1}, p1), (Sub{a2, b2}, p2))

assert Expr.copy.mul:
  forall -a: Expr
  forall -b: Expr
  forall ca: Copy(Expr, a) & Copy(Expr, a)
  forall cb: Copy(Expr, b) & Copy(Expr, b)
  Copy(Expr, Mul{a, b}) & Copy(Expr, Mul{a, b})

def Expr.copy.mul(a, b, ca, cb):
  ((a1, ea1), (a2, ea2)) = ca
  ((b1, eb1), (b2, eb2)) = cb
  p1 = Equal.trans(Expr, Mul{a, b}, Mul{a1, b}, Mul{a1, b1}, Equal.cong(Expr, Expr, x => Mul{x, b}, a, a1, ea1), Equal.cong(Expr, Expr, x => Mul{a1, x}, b, b1, eb1))
  p2 = Equal.trans(Expr, Mul{a, b}, Mul{a2, b}, Mul{a2, b2}, Equal.cong(Expr, Expr, x => Mul{x, b}, a, a2, ea2), Equal.cong(Expr, Expr, x => Mul{a2, x}, b, b2, eb2))
  ((Mul{a1, b1}, p1), (Mul{a2, b2}, p2))

assert Expr.copy.xor:
  forall -a: Expr
  forall -b: Expr
  forall ca: Copy(Expr, a) & Copy(Expr, a)
  forall cb: Copy(Expr, b) & Copy(Expr, b)
  Copy(Expr, Xor{a, b}) & Copy(Expr, Xor{a, b})

def Expr.copy.xor(a, b, ca, cb):
  ((a1, ea1), (a2, ea2)) = ca
  ((b1, eb1), (b2, eb2)) = cb
  p1 = Equal.trans(Expr, Xor{a, b}, Xor{a1, b}, Xor{a1, b1}, Equal.cong(Expr, Expr, x => Xor{x, b}, a, a1, ea1), Equal.cong(Expr, Expr, x => Xor{a1, x}, b, b1, eb1))
  p2 = Equal.trans(Expr, Xor{a, b}, Xor{a2, b}, Xor{a2, b2}, Equal.cong(Expr, Expr, x => Xor{x, b}, a, a2, ea2), Equal.cong(Expr, Expr, x => Xor{a2, x}, b, b2, eb2))
  ((Xor{a1, b1}, p1), (Xor{a2, b2}, p2))

assert Expr.copy:
  forall e: Expr
  Copy(Expr, e) & Copy(Expr, e)

def Expr.copy(e):
  match e:
    case Var{}:
      ((Var{}, {==}), (Var{}, {==}))
    case Lit{v}:
      Expr.copy.lit(v, U32.copy(v))
    case Add{a, b}:
      Expr.copy.add(a, b, Expr.copy(a), Expr.copy(b))
    case Sub{a, b}:
      Expr.copy.sub(a, b, Expr.copy(a), Expr.copy(b))
    case Mul{a, b}:
      Expr.copy.mul(a, b, Expr.copy(a), Expr.copy(b))
    case Xor{a, b}:
      Expr.copy.xor(a, b, Expr.copy(a), Expr.copy(b))

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

assert sel.go:
  forall x: U32
  forall y: U32
  forall z: Bool
  U32

def sel.go(x, y, z):
  match z:
    case True{}:
      x
    case False{}:
      y

assert sel:
  forall t: U32
  forall x: U32
  forall y: U32
  U32

def sel(t, x, y):
  sel.go(x, y, U32.is_zero(t))

assert adiff:
  forall +a: +U32
  forall +b: +U32
  U32

def adiff(a, b):
  sel(b2u(U32.is_lt(a, b)), U32.sub(a, b), U32.sub(b, a))

assert node:
  forall o: Nat
  forall a: Expr
  forall b: Expr
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
assert gen.leaf:
  forall +h: +U32
  forall z: Bool
  Expr

assert gen:
  forall +d: +Nat
  forall +h: +U32
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
      gen.leaf(h, U32.is_zero(U32.and(U32.shrn(8n, h), 1)))
    case 1n+p:
      a = gen(p, prng(U32.xor(h, 2654435761)))
      b = gen(p, prng(U32.add(h, 340573321)))
      node(U32.to_nat(U32.mod(h, 4)), a, b)

# pattern-matching interpreter reading the shared tree
assert eval:
  forall e: Expr
  forall +x: +U32
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
assert esize:
  forall e: Expr
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
assert floop:
  forall +j: +Nat
  forall +e: +Expr
  forall acc: U32
  U32

def floop(j, e, acc):
  match j:
    case 0n:
      U32.add(acc, U32.mul(esize(e), 8))
    case 1n+p:
      +xx = {U32.from_nat(p) : +U32}
      v = eval(e, xx)
      t = U32.add(U32.mul(xx, xx), U32.add(U32.mul(3, xx), 7))
      floop(p, e, U32.add(acc, adiff(v, t)))

assert cand:
  forall +s: +U32
  forall pts: Nat
  Sel

def cand(s, pts):
  t = gen(5n, prng(s))
  +f = {floop(pts, t, 0) : +U32}
  Sel{f, s, U32.xor(f, U32.mul(s, 2654435761))}

# tournament: keep the lower-fitness candidate, sum the checksums
assert pick:
  forall a: Sel
  forall b: Sel
  Sel

def pick(a, b):
  match a b:
    case Sel{f1, s1, c1} Sel{f2, s2, c2}:
      +g1 = {f1 : +U32}
      +g2 = {f2 : +U32}
      +w = {b2u(U32.is_lt(g1, g2)) : +U32}
      Sel{sel(w, g2, g1), sel(w, s2, s1), U32.add(c1, c2)}

assert batch:
  forall +d: +Nat
  forall +s: +U32
  forall +pts: +Nat
  Sel

def batch(d, s, pts):
  match d:
    case 0n:
      cand(prng(s), pts)
    case 1n+p:
      a b = batch(p, U32.add(U32.mul(s, 1664525), 1), pts) batch(p, U32.add(U32.mul(s, 214013), 3), pts)
      pick(a, b)

# hill-climb the tournament winner: mutate the seed, keep improvements
assert climb:
  forall +r: +Nat
  forall +bs: +U32
  forall +bf: +U32
  forall +pts: +Nat
  U32

def climb(r, bs, bf, pts):
  match r:
    case 0n:
      U32.xor(bf, U32.mul(bs, 2654435761))
    case 1n+p:
      +cn = {cand(prng(U32.xor(bs, U32.mul(U32.inc(U32.from_nat(p)), 40503))), pts) : +Sel ~ Sel.copy}
      +ff = {Sel.fit(cn) : +U32}
      +w = {b2u(U32.is_lt(ff, bf)) : +U32}
      climb(p, sel(w, bs, Sel.seed(cn)), sel(w, bf, ff), pts)

assert run.fin:
  forall r: Nat
  forall +p: +Nat
  forall t: Sel
  U32

assert run:
  forall d: Nat
  forall s0: U32
  forall r: Nat
  forall +p: +Nat
  U32

def run.fin(r, p, t):
  match t:
    case Sel{f, s, c}:
      U32.add(climb(r, s, f, p), c)

def run(d, s0, r, p):
  run.fin(r, p, batch(d, s0, p))

assert size:
  Nat

def size():
  18n

assert pts:
  Nat

def pts():
  110n

# small: run!(6n, 42, 32n, 16n) expect 2490246820; big expect 2383953211
assert main:
  IO(Unit)

def main():
  IO.print(U32.show(run!(size(), 42, 32n, pts())))
