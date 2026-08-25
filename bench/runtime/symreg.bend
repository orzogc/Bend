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

# copy witness for the shared tree: never emitted, only licenses +Expr
assert Expr.copy:
  forall e: Expr
  Copy(Expr, e) & Copy(Expr, e)

def Expr.copy(e):
  match e:
    case Var{}:
      ((Var{}, {==}), (Var{}, {==}))
    case Lit{v}:
      ((v1, e1), (v2, e2)) = U32.copy(v)
      p1 = Equal.cong(U32, Expr, x => Lit{x}, v, v1, e1)
      p2 = Equal.cong(U32, Expr, x => Lit{x}, v, v2, e2)
      ((Lit{v1}, p1), (Lit{v2}, p2))
    case Add{a, b}:
      ((a1, ea1), (a2, ea2)) = Expr.copy(a)
      ((b1, eb1), (b2, eb2)) = Expr.copy(b)
      p1 = Equal.trans(Expr, Add{a, b}, Add{a1, b}, Add{a1, b1}, Equal.cong(Expr, Expr, x => Add{x, b}, a, a1, ea1), Equal.cong(Expr, Expr, x => Add{a1, x}, b, b1, eb1))
      p2 = Equal.trans(Expr, Add{a, b}, Add{a2, b}, Add{a2, b2}, Equal.cong(Expr, Expr, x => Add{x, b}, a, a2, ea2), Equal.cong(Expr, Expr, x => Add{a2, x}, b, b2, eb2))
      ((Add{a1, b1}, p1), (Add{a2, b2}, p2))
    case Sub{a, b}:
      ((a1, ea1), (a2, ea2)) = Expr.copy(a)
      ((b1, eb1), (b2, eb2)) = Expr.copy(b)
      p1 = Equal.trans(Expr, Sub{a, b}, Sub{a1, b}, Sub{a1, b1}, Equal.cong(Expr, Expr, x => Sub{x, b}, a, a1, ea1), Equal.cong(Expr, Expr, x => Sub{a1, x}, b, b1, eb1))
      p2 = Equal.trans(Expr, Sub{a, b}, Sub{a2, b}, Sub{a2, b2}, Equal.cong(Expr, Expr, x => Sub{x, b}, a, a2, ea2), Equal.cong(Expr, Expr, x => Sub{a2, x}, b, b2, eb2))
      ((Sub{a1, b1}, p1), (Sub{a2, b2}, p2))
    case Mul{a, b}:
      ((a1, ea1), (a2, ea2)) = Expr.copy(a)
      ((b1, eb1), (b2, eb2)) = Expr.copy(b)
      p1 = Equal.trans(Expr, Mul{a, b}, Mul{a1, b}, Mul{a1, b1}, Equal.cong(Expr, Expr, x => Mul{x, b}, a, a1, ea1), Equal.cong(Expr, Expr, x => Mul{a1, x}, b, b1, eb1))
      p2 = Equal.trans(Expr, Mul{a, b}, Mul{a2, b}, Mul{a2, b2}, Equal.cong(Expr, Expr, x => Mul{x, b}, a, a2, ea2), Equal.cong(Expr, Expr, x => Mul{a2, x}, b, b2, eb2))
      ((Mul{a1, b1}, p1), (Mul{a2, b2}, p2))
    case Xor{a, b}:
      ((a1, ea1), (a2, ea2)) = Expr.copy(a)
      ((b1, eb1), (b2, eb2)) = Expr.copy(b)
      p1 = Equal.trans(Expr, Xor{a, b}, Xor{a1, b}, Xor{a1, b1}, Equal.cong(Expr, Expr, x => Xor{x, b}, a, a1, ea1), Equal.cong(Expr, Expr, x => Xor{a1, x}, b, b1, eb1))
      p2 = Equal.trans(Expr, Xor{a, b}, Xor{a2, b}, Xor{a2, b2}, Equal.cong(Expr, Expr, x => Xor{x, b}, a, a2, ea2), Equal.cong(Expr, Expr, x => Xor{a2, x}, b, b2, eb2))
      ((Xor{a1, b1}, p1), (Xor{a2, b2}, p2))

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
assert gen:
  forall +d: +Nat
  forall +h: +U32
  Expr

def gen(d, h):
  match d:
    case 0n:
      match U32.is_zero(U32.and(U32.shrn(8n, h), 1)):
        case True{}:
          Var{}
        case False{}:
          Lit{U32.and(h, 255)}
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
      Both{a, b} = {Both{batch(p, U32.add(U32.mul(s, 1664525), 1), pts), batch(p, U32.add(U32.mul(s, 214013), 3), pts)} : Par<Sel, Sel>}
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
      match cand(prng(U32.xor(bs, U32.mul(U32.inc(U32.from_nat(p)), 40503))), pts):
        case Sel{f2, s2, c2}:
          +ff = {f2 : +U32}
          +w = {b2u(U32.is_lt(ff, bf)) : +U32}
          climb(p, sel(w, bs, s2), sel(w, bf, ff), pts)

assert run:
  forall d: Nat
  forall s0: U32
  forall r: Nat
  forall +p: +Nat
  U32

def run(d, s0, r, p):
  match batch(d, s0, p):
    case Sel{f, s, c}:
      U32.add(climb(r, s, f, p), c)

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
