import Base
# Hashmap: a hash table with separate chaining, the suite's
# arrays-of-boxed-elements case. A table is an Array of 4096 buckets,
# each a Chain of keys: a recursive Data type, so every slot holds a
# boxed heap value, not a flat word or record. 2^S independent tables
# fork as a balanced batch tree; table t seeds from its hashed index.
# Phase 1 inserts D keys: key j is the xorshift hash of the seed and
# j, masked to 20 bits (so duplicates occur); its low 12 bits pick the
# bucket; the insert reads the bucket's chain, walks it, and, when the
# key is absent, conses the key onto the chain and writes it back (a
# present key leaves the bucket untouched). Phase 2 looks up D probe
# keys drawn from a second seed over the same key space: each walk
# finds or misses, and the hits are counted. The table checksum mixes
# the hit count, the distinct-key count (the chain lengths summed) and
# a position-weighted fold over the chain lengths; table checksums sum
# up the fork tree.
#
# This is a defective case by design: Array.get hands the bucket's
# chain back as a value while the array keeps its own, the walk opens
# that value node by node, and the write-back swaps a fresh cons into
# the slot, where C walks an index-linked node pool in place and
# pushes one node at the head. The gap is the point; the program is
# spelled the natural way anyway.
#
# Spelling notes: Chain is a local Data type (Base's List<U32> is
# affine, of kind Type, so Array.get refuses it as an element). A
# chain walk carries its last comparison as a Bool column after the
# chain (a match follows binder order, and only the chain column may
# shrink), so a found key stops the walk one node late. Array.get's
# (array, element) pair rides into the next stage def as a parameter;
# loop counters are Nats (no U32 match in Bend4) with the U32 index
# alongside; a chain read once and used twice (walked, then consed
# onto) rides a + binder. Knobs: tables (S, 2^S tables, 2x per notch)
# and keys (D, inserts and lookups per table, the fine linear knob).
#
# Sizes (S, D): small (2n, 256) expect 4206244792 (verified against
# the C twin), big (11n, 16384) expect 1307803744.

type Chain is Data:
  CNil{}
  CCons{k: U32, t: Chain}

assert b2u:
  forall b: Bool
  U32

def b2u(b):
  match b:
    case False{}:
      0
    case True{}:
      1

# xorshift: x ^= x<<13; x ^= x>>17; x ^= x<<5
assert prng:
  forall +x: U32
  U32

def prng(x):
  +b = U32.xor(x, U32.shln(x, 13n))
  +d = U32.xor(b, U32.shrn(b, 17n))
  U32.xor(d, U32.shln(d, 5n))

# a key: the hash of a seed and a draw index, masked to 20 bits
assert key:
  forall s: U32
  forall j: U32
  U32

def key(s, j):
  h = prng(U32.xor(U32.mul(U32.inc(j), 2654435761), U32.mul(s, 340573321)))
  U32.and(h, 1048575)

# the chain walk: the last comparison rides in as f, so the walk
# stops one node past a found key
assert has:
  forall c: Chain
  forall +k: U32
  forall f: Bool
  Bool

def has(c, k, f):
  match c f:
    case _ True{}:
      True{}
    case CNil{} False{}:
      False{}
    case CCons{h, t} False{}:
      has(t, k, U32.is_eq(h, k))

# a chain's length
assert len:
  forall c: Chain
  forall acc: U32
  U32

def len(c, acc):
  match c:
    case CNil{}:
      acc
    case CCons{h, t}:
      len(t, U32.inc(acc))

# the insert's decision: a present key leaves the bucket untouched,
# an absent one is consed onto the chain and written back
assert ins.put:
  forall a: Array<Chain>
  forall b: U32
  forall k: U32
  forall c: Chain
  forall found: Bool
  Array<Chain>

def ins.put(a, b, k, c, found):
  match found:
    case True{}:
      a
    case False{}:
      Array.set(Chain, a, b, CCons{k, c})

# one insert: the bucket's (array, chain) read pair arrives as a
# parameter; the chain is walked, then consed onto when the key is
# absent
assert ins:
  forall +b: U32
  forall +k: U32
  forall r: Array<Chain> & Chain
  Array<Chain>

def ins(b, k, r):
  (a, c0) = r
  +c = c0
  ins.put(a, b, k, c, has(c, k, False{}))

# phase 1: D inserts, key j from the table seed
assert fill:
  forall n: Nat
  forall +s: U32
  forall +j: U32
  forall a: Array<Chain>
  Array<Chain>

def fill(n, s, j, a):
  match n:
    case 0n:
      a
    case 1n+p:
      +k = key(s, j)
      +b = U32.and(k, 4095)
      fill(p, s, U32.inc(j), ins(b, k, Array.get(Chain, a, b)))

# one lookup: walk the bucket's chain, count a hit
assert probe:
  forall k: U32
  forall hits: U32
  forall r: Array<Chain> & Chain
  Array<Chain> & U32

def probe(k, hits, r):
  (a, c) = r
  (a, U32.add(hits, b2u(has(c, k, False{}))))

# phase 2: D lookups, probe key j from the second seed; the (array,
# hits) pair rides as r
assert look:
  forall n: Nat
  forall +s: U32
  forall +j: U32
  forall r: Array<Chain> & U32
  Array<Chain> & U32

def look(n, s, j, r):
  match n:
    case 0n:
      r
    case 1n+p:
      (a, hits) = r
      +k = key(s, j)
      b = U32.and(k, 4095)
      look(p, s, U32.inc(j), probe(k, hits, Array.get(Chain, a, b)))

# one bucket into the sweep: its length adds to the distinct count
# and mixes position-weighted into acc
assert bmix:
  forall i: U32
  forall cnt: U32
  forall acc: U32
  forall r: Array<Chain> & Chain
  Array<Chain> & U32 & U32

def bmix(i, cnt, acc, r):
  (a, c) = r
  +l = len(c, 0)
  m = U32.xor(U32.mul(acc, 2654435761), U32.mul(l, U32.add(i, 3)))
  (a, U32.add(cnt, l), m)

# the bucket sweep, ascending: the (array, distinct, acc) triple rides
# as r
assert sweep:
  forall n: Nat
  forall +i: U32
  forall r: Array<Chain> & U32 & U32
  U32 & U32

def sweep(n, i, r):
  match n:
    case 0n:
      (a, cnt, acc) = r
      (cnt, acc)
    case 1n+p:
      (a, cnt, acc) = r
      sweep(p, U32.inc(i), bmix(i, cnt, acc, Array.get(Chain, a, i)))

# the table checksum: the sweep's (distinct, acc) pair mixed with the
# hit count
assert finish:
  forall hits: U32
  forall m: U32 & U32
  U32

def finish(hits, m):
  (cnt, acc) = m
  U32.add(U32.xor(acc, U32.mul(hits, 2654435761)), U32.mul(cnt, 340573321))

assert table.fin:
  forall r: Array<Chain> & U32
  U32

def table.fin(r):
  (a, hits) = r
  finish(hits, sweep(4096n, 0, (a, 0, 0)))

# one table: a fresh 4096-bucket array, D inserts from the table seed,
# D lookups from the second seed, the bucket sweep
assert table:
  forall t: U32
  forall +d: Nat
  U32

def table(t, d):
  +s = U32.mul(U32.inc(t), 2654435761)
  a = fill(d, s, 0, Array.new(Chain, 12n, CNil{}))
  table.fin(look(d, prng(s), 0, (a, 0)))

# batch tree over the table index space: table checksums sum up
assert batch:
  forall +p: Nat
  forall +t: U32
  forall +d: Nat
  U32

def batch(p, t, d):
  match p:
    case 0n:
      table(t, d)
    case 1n+q:
      a b = batch(q, t, d) batch(q, U32.add(t, U32.shln(1, q)), d)
      U32.add(a, b)

assert tables:
  Nat

def tables():
  11n

assert keys:
  Nat

def keys():
  U32.to_nat(16384)

# small: batch!(2n, 0, U32.to_nat(256)) expect 4206244792; big:
# batch!(tables(), 0, keys()) expect 1307803744
assert main:
  IO(Unit)

def main():
  IO.print(U32.show(batch!(tables(), 0, keys())))
