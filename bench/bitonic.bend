#[halts]
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

type Tree:
  Leaf{v: U32}
  Node{l: Tree, r: Tree}

type Stat:
  St{lo: U32, hi: U32, ok: U32, mx: U32}

# xorshift: x ^= x<<13; x ^= x>>17; x ^= x<<5
def prng(+x: U32) -> U32:
  +b = U32.xor(x, U32.shln(13n, x))
  +d = U32.xor(b, U32.shrn(17n, b))
  U32.xor(d, U32.shln(5n, d))

# leaf key: hash of the leaf index
def key(i: U32) -> U32:
  prng(U32.mul(U32.inc(i), 2654435761))

# compare-and-swap of two leaves; s flips the order (Bend3's
# swap(s ^ (x > y), x, y))
def warp_leaf(+x: U32, +y: U32, s: Bool) -> Tree:
  match Bool.xor(s, U32.is_gt(x, y)):
    case False{}:
      Node{Leaf{x}, Leaf{y}}
    case True{}:
      Node{Leaf{y}, Leaf{x}}

def warp_zip(wa: Tree, wb: Tree) -> Tree:
  match wa wb:
    case Node{a0, a1} Node{b0, b1}:
      Node{Node{a0, b0}, Node{a1, b1}}
    case Node{a0, a1} Leaf{bv}:
      Leaf{0}
    case Leaf{av} Node{b0, b1}:
      Leaf{0}
    case Leaf{av} Leaf{bv}:
      Leaf{0}

def warp(a: Tree, b: Tree, +s: Bool) -> Tree:
  match a b:
    case Leaf{av} Leaf{bv}:
      warp_leaf(av, bv, s)
    case Leaf{av} Node{ba, bb}:
      Leaf{0}
    case Node{aa, ab} Leaf{bv}:
      Leaf{0}
    case Node{aa, ab} Node{ba, bb}:
      Both{wa, wb} = {Both{warp(aa, ba, s), warp(ab, bb, s)} : Par<Tree, Tree>}
      warp_zip(wa, wb)

# bitonic merge of a tree of depth 1+d: warp the root pair, then merge
# both halves one level shallower (Bend3's flow/down cycle, folded)
def flow(+d: Nat, +s: Bool, t: Tree) -> Tree:
  match d t:
    case 0n Leaf{v}:
      Leaf{v}
    case 0n Node{a, b}:
      warp(a, b, s)
    case 1n+p Leaf{v}:
      Leaf{v}
    case 1n+p Node{a, b}:
      match warp(a, b, s):
        case Leaf{v}:
          Leaf{v}
        case Node{wa, wb}:
          Both{fa, fb} = {Both{flow(p, s, wa), flow(p, s, wb)} : Par<Tree, Tree>}
          Node{fa, fb}

# fused build-and-sort: 2^d leaves keyed by index, halves sorted in
# opposite directions, then merged by flow
def bsort(+d: Nat, s: Bool, +x: U32) -> Tree:
  match d:
    case 0n:
      Leaf{key(x)}
    case 1n+p:
      Both{sa, sb} = {Both{bsort(p, False{}, U32.inc(U32.shl(x))), bsort(p, True{}, U32.shl(x))} : Par<Tree, Tree>}
      flow(p, s, Node{sa, sb})

# verification join: bounds ride outward, ok demands left.hi <=
# right.lo, the mix is order-sensitive
def stat_join(a: Stat, b: Stat) -> Stat:
  match a b:
    case St{alo, ahi, aok, amx} St{blo, bhi, bok, bmx}:
      match U32.is_le(ahi, blo):
        case False{}:
          St{alo, bhi, 0, U32.add(U32.mul(amx, 2654435761), bmx)}
        case True{}:
          St{alo, bhi, U32.and(aok, bok), U32.add(U32.mul(amx, 2654435761), bmx)}

# rank-summary scan over the sorted tree
def scan(t: Tree) -> Stat:
  match t:
    case Leaf{v}:
      +w = v
      St{w, w, 1, w}
    case Node{a, b}:
      Both{l, r} = {Both{scan(a), scan(b)} : Par<Stat, Stat>}
      stat_join(l, r)

def stat_out(s: Stat) -> U32:
  match s:
    case St{lo, hi, ok, mx}:
      U32.add(U32.xor(U32.mul(mx, 2654435761), U32.add(hi, U32.mul(lo, 340573321))), U32.mul(ok, 2246822519))

def size.small() -> Nat:
  8n

def expect.small() -> U32:
  971629740

def size.big() -> Nat:
  23n

def expect.big() -> U32:
  3787129428

def main() -> U32:
  t = bsort!(23n, False{}, 0)
  stat_out(scan!(t))
