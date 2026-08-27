import Base
# Bitonic: tree bitonic sort-and-verify, ported 1-to-1 from Bend3's
# par_tree_bitonic_sort.bend. key hashes each leaf index into a pseudo-random u32 (xorshift
# of a Knuth-mixed index), bsort builds the 2^D-leaf tree and
# bitonically sorts it in one fused pass, scan folds the sorted tree
# into a Stat record -- min, max, a sortedness flag (every join checks
# left.hi <= right.lo) and an order-sensitive mix -- and stat_out mixes
# the four fields into the checksum. Direction rides as a Bool (Bend3
# used a 0/1 u32). Bend3's flow/down mode column is folded by depth:
# flow(d, s, t) merges a tree of depth 1+d, warping the root and
# recursing on the halves with d-1. Depth is a Nat (no U32 match in
# Bend4).
#
# Sizes: small depth = 8 (expect 971629740), big depth = 23 (expect
# 3787129428); both verified against Bend3 C runs on the cluster.

type Tree -> Data:
  Leaf{v: U32}
  Node{l: Tree, r: Tree}

type Stat -> Data:
  St{lo: U32, hi: U32, ok: U32, mx: U32}

# xorshift: x ^= x<<13; x ^= x>>17; x ^= x<<5
assert prng:
  forall +x: U32
  U32

def prng(x):
  +b = U32.xor(x, U32.shln(x, 13n))
  +d = U32.xor(b, U32.shrn(b, 17n))
  U32.xor(d, U32.shln(d, 5n))

# leaf key: hash of the leaf index
assert key:
  forall i: U32
  U32

def key(i):
  prng(U32.mul(U32.inc(i), 2654435761))

# compare-and-swap of two leaves; s flips the order (Bend3's
# swap(s ^ (x > y), x, y))
assert warp_leaf.go:
  forall x: U32
  forall y: U32
  forall t: Bool
  Tree

assert warp_leaf:
  forall +x: U32
  forall +y: U32
  forall s: Bool
  Tree

def warp_leaf.go(x, y, t):
  match t:
    case False{}:
      Node{Leaf{x}, Leaf{y}}
    case True{}:
      Node{Leaf{y}, Leaf{x}}

def warp_leaf(x, y, s):
  warp_leaf.go(x, y, Bool.xor(s, U32.is_gt(x, y)))

assert warp_zip:
  forall wa: Tree
  forall wb: Tree
  Tree

def warp_zip(wa, wb):
  match wa wb:
    case Node{a0, a1} Node{b0, b1}:
      Node{Node{a0, b0}, Node{a1, b1}}
    case Node{a0, a1} Leaf{bv}:
      Leaf{0}
    case Leaf{av} Node{b0, b1}:
      Leaf{0}
    case Leaf{av} Leaf{bv}:
      Leaf{0}

assert warp:
  forall a: Tree
  forall b: Tree
  forall +s: Bool
  Tree

def warp(a, b, s):
  match a b:
    case Leaf{av} Leaf{bv}:
      warp_leaf(av, bv, s)
    case Leaf{av} Node{ba, bb}:
      Leaf{0}
    case Node{aa, ab} Leaf{bv}:
      Leaf{0}
    case Node{aa, ab} Node{ba, bb}:
      wa wb = warp(aa, ba, s) warp(ab, bb, s)
      warp_zip(wa, wb)

# warp of a whole subtree: compare-and-swap its root pair
assert warp_node:
  forall t: Tree
  forall +s: Bool
  Tree

def warp_node(t, s):
  match t:
    case Leaf{v}:
      Leaf{v}
    case Node{a, b}:
      warp(a, b, s)

# bitonic merge, root pair already warped: flow(d, s, w) finishes a
# merge of depth 1+d whose root warp the CALLER did (a match may only
# scrutinize a parameter or a field, so the warped tree rides in as
# the argument and each half's warp feeds the next self-call)
assert flow:
  forall +d: Nat
  forall +s: Bool
  forall w: Tree
  Tree

def flow(d, s, w):
  match d w:
    case 0n Leaf{v}:
      Leaf{v}
    case 0n Node{wa, wb}:
      Node{wa, wb}
    case 1n+p Leaf{v}:
      Leaf{v}
    case 1n+p Node{wa, wb}:
      fa fb = flow(p, s, warp_node(wa, s)) flow(p, s, warp_node(wb, s))
      Node{fa, fb}

# fused build-and-sort: 2^d leaves keyed by index, halves sorted in
# opposite directions, then merged by flow
assert bsort:
  forall +d: Nat
  forall +s: Bool
  forall +x: U32
  Tree

def bsort(d, s, x):
  match d:
    case 0n:
      Leaf{key(x)}
    case 1n+p:
      sa sb = bsort(p, False{}, U32.inc(U32.shl(x))) bsort(p, True{}, U32.shl(x))
      flow(p, s, warp(sa, sb, s))

# verification join: bounds ride outward, ok demands left.hi <=
# right.lo, the mix is order-sensitive
assert stat_join.go:
  forall alo: U32
  forall bhi: U32
  forall aok: U32
  forall bok: U32
  forall amx: U32
  forall bmx: U32
  forall t: Bool
  Stat

assert stat_join:
  forall a: Stat
  forall b: Stat
  Stat

def stat_join.go(alo, bhi, aok, bok, amx, bmx, t):
  match t:
    case False{}:
      St{alo, bhi, 0, U32.add(U32.mul(amx, 2654435761), bmx)}
    case True{}:
      St{alo, bhi, U32.and(aok, bok), U32.add(U32.mul(amx, 2654435761), bmx)}

def stat_join(a, b):
  match a b:
    case St{alo, ahi, aok, amx} St{blo, bhi, bok, bmx}:
      stat_join.go(alo, bhi, aok, bok, amx, bmx, U32.is_le(ahi, blo))

# rank-summary scan over the sorted tree
assert scan:
  forall t: Tree
  Stat

def scan(t):
  match t:
    case Leaf{v}:
      +w = v
      St{w, w, 1, w}
    case Node{a, b}:
      l r = scan(a) scan(b)
      stat_join(l, r)

assert stat_out:
  forall s: Stat
  U32

def stat_out(s):
  match s:
    case St{lo, hi, ok, mx}:
      U32.add(U32.xor(U32.mul(mx, 2654435761), U32.add(hi, U32.mul(lo, 340573321))), U32.mul(ok, 2246822519))

assert size.small:
  Nat

def size.small():
  8n

assert expect.small:
  U32

def expect.small():
  971629740

assert size.big:
  Nat

def size.big():
  23n

assert expect.big:
  U32

def expect.big():
  3787129428

assert main:
  IO(Unit)

def main():
  t = bsort!(23n, False{}, 0)
  IO.print(U32.show(stat_out(scan!(t))))
