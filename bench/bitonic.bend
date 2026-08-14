import Base
# Bitonic: tree bitonic sort-and-verify, ported from Bend3's
# par_tree_bitonic_sort.bend. key hashes each leaf index into a
# pseudo-random u32 (xorshift of a Knuth-mixed index), bsort builds the
# 2^D-leaf tree and bitonically sorts it in one fused pass, scan folds
# the sorted tree into a Stat record -- min, max, a sortedness flag
# (every join checks left.hi <= right.lo) and an order-sensitive mix --
# and stat_out mixes the four fields into the checksum. Direction rides
# as a Bool (Bend3 used a 0/1 u32).
#
# Bend3's flow/down call cycle is folded here by depth instead of by a
# mode column: flow(d, s, t) merges a tree of depth 1+d, warping the
# root and recursing on the halves with d-1. bsort carries the depth
# TWICE (d and e, always equal) because each recursive argument must be
# a direct subterm or one Nat.copy away from the pattern variable, and
# the node case needs the predecessor three ways (two children + merge).
#
# Sizes: small depth = 8 (expect 971629740), big depth = 23
# (expect 3787129428, verified against Bend3).

type Tree:
  Leaf{v: U32}
  Node{l: Tree, r: Tree}

type Stat:
  St{lo: U32, hi: U32, ok: U32, mx: U32}

# u32 constant from base-2^10 digits: a*2^20 + b*2^10 + c
def u32d(a: Nat, b: Nat, c: Nat) -> U32:
  U32.add(U32.shln(20n, U32.from_nat(a)), U32.add(U32.shln(10n, U32.from_nat(b)), U32.from_nat(c)))

# 2654435761 = 0x9E3779B1 (Knuth multiplicative hash)
def knuth() -> U32:
  u32d(2531n, 478n, 433n)

# 340573321 = 0x144CBC89
def cmix() -> U32:
  u32d(324n, 815n, 137n)

# 2246822519 = 0x85EBCA77
def cok() -> U32:
  u32d(2142n, 754n, 631n)

# xorshift: x ^= x<<13; x ^= x>>17; x ^= x<<5
def prng(x: U32) -> U32:
  ((x1, ex1), (x2, ex2)) = U32.copy(x)
  ((b1, eb1), (b2, eb2)) = U32.copy(U32.xor(x1, U32.shln(13n, x2)))
  ((d1, ed1), (d2, ed2)) = U32.copy(U32.xor(b1, U32.shrn(17n, b2)))
  U32.xor(d1, U32.shln(5n, d2))

# leaf key: hash of the leaf index
def key(i: U32) -> U32:
  prng(U32.mul(U32.inc(i), knuth()))

# compare-and-swap of two leaves; s flips the order (Bend3's
# swap(s ^ (x > y), x, y))
def warp_leaf(x: U32, y: U32, s: Bool) -> Tree:
  ((x1, ex1), (x2, ex2)) = U32.copy(x)
  ((y1, ey1), (y2, ey2)) = U32.copy(y)
  match Bool.xor(s, U32.is_gt(x1, y1)):
    case False{}:
      Node{Leaf{x2}, Leaf{y2}}
    case True{}:
      Node{Leaf{y2}, Leaf{x2}}

def warp_zip(wa: Tree, wb: Tree) -> Tree:
  match wa wb:
    case Node{a0, a1} Node{b0, b1}:
      Node{Node{a0, b0}, Node{a1, b1}}
    case Node{a0, a1} Leaf{bv}:
      Leaf{U32.zero()}
    case Leaf{av} Node{b0, b1}:
      Leaf{U32.zero()}
    case Leaf{av} Leaf{bv}:
      Leaf{U32.zero()}

def warp(a: Tree, b: Tree, s: Bool) -> Tree:
  match a b:
    case Leaf{av} Leaf{bv}:
      warp_leaf(av, bv, s)
    case Leaf{av} Node{ba, bb}:
      Leaf{U32.zero()}
    case Node{aa, ab} Leaf{bv}:
      Leaf{U32.zero()}
    case Node{aa, ab} Node{ba, bb}:
      ((s1, es1), (s2, es2)) = Bool.copy(s)
      warp_zip(warp(aa, ba, s1), warp(ab, bb, s2))

# bitonic merge of a tree of depth 1+d: warp the root pair, then merge
# both halves one level shallower (Bend3's flow/down cycle, folded)
def flow(d: Nat, s: Bool, t: Tree) -> Tree:
  match d t:
    case 0n Leaf{v}:
      Leaf{v}
    case 0n Node{a, b}:
      warp(a, b, s)
    case 1n+p Leaf{v}:
      Leaf{v}
    case 1n+p Node{a, b}:
      ((p1, e1), (p2, e2)) = Nat.copy(p)
      ((s0, es0), (s12, es12)) = Bool.copy(s)
      ((s1, es1), (s2, es2)) = Bool.copy(s12)
      match warp(a, b, s0):
        case Leaf{v}:
          Leaf{v}
        case Node{wa, wb}:
          Node{flow(p1, s1, wa), flow(p2, s2, wb)}

# fused build-and-sort: 2^d leaves keyed by index, halves sorted in
# opposite directions, then merged by flow. e mirrors d (see header).
def bsort(d: Nat, e: Nat, s: Bool, x: U32) -> Tree:
  match d:
    case 0n:
      Leaf{key(x)}
    case 1n+p:
      match e:
        case 0n:
          Leaf{U32.zero()}
        case 1n+q:
          ((pa, ea), (pb, eb)) = Nat.copy(p)
          ((qa, ec), (qb, ed)) = Nat.copy(q)
          ((qb1, ee), (qb2, ef)) = Nat.copy(qb)
          ((x1, ex1), (x2, ex2)) = U32.copy(x)
          flow(qb2, s, Node{bsort(pa, qa, False{}, U32.inc(U32.shl(x1))), bsort(pb, qb1, True{}, U32.shl(x2))})

# verification join: bounds ride outward, ok demands left.hi <=
# right.lo, the mix is order-sensitive
def stat_join(a: Stat, b: Stat) -> Stat:
  match a b:
    case St{alo, ahi, aok, amx} St{blo, bhi, bok, bmx}:
      match U32.is_le(ahi, blo):
        case False{}:
          St{alo, bhi, U32.zero(), U32.add(U32.mul(amx, knuth()), bmx)}
        case True{}:
          St{alo, bhi, U32.and(aok, bok), U32.add(U32.mul(amx, knuth()), bmx)}

# rank-summary scan over the sorted tree
def scan(t: Tree) -> Stat:
  match t:
    case Leaf{v}:
      ((v1, e1), (v2, e2)) = U32.copy(v)
      ((v3, e3), (v4, e4)) = U32.copy(v2)
      St{v1, v3, U32.one(), v4}
    case Node{a, b}:
      stat_join(scan(a), scan(b))

def stat_out(s: Stat) -> U32:
  match s:
    case St{lo, hi, ok, mx}:
      U32.add(U32.xor(U32.mul(mx, knuth()), U32.add(hi, U32.mul(lo, cmix()))), U32.mul(ok, cok()))

def bench(d: Nat) -> U32:
  ((d1, e1), (d2, e2)) = Nat.copy(d)
  stat_out(scan(bsort(d1, d2, False{}, U32.zero())))

def size.small() -> Nat:
  8n

def expect.small() -> U32:
  u32d(926n, 633n, 172n)

def size.big() -> Nat:
  23n

def expect.big() -> U32:
  u32d(3611n, 704n, 596n)

def main() -> Bool:
  U32.is_eq(bench(size.small()), expect.small())
