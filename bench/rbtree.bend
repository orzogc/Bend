import Base
# RBTree benchmark (port of bend3 seq_hvm_rbtree). Okasaki
# insert-balance on a U32-keyed set: p passes of 2^k sequential keys
# (passes 2..p hit the EQ/replace path), then 2^a + 2^b extra keys,
# then an in-order fold with mix(h, k) = rotl1(h) + k, seeded at 0.
# main checks the checksum against the known constant, returns Bool.
#
# Sizes (p, k, a, b): small (3, 6, 3, 2) expect 4763;
# big (19, 18, 15, 14) (~5.03M inserts) expect 3493273599.

# u32 constant from base-2^10 digits: a*2^20 + b*2^10 + c
def u32d(a: Nat, b: Nat, c: Nat) -> U32:
  U32.add(U32.shln(20n, U32.from_nat(a)), U32.add(U32.shln(10n, U32.from_nat(b)), U32.from_nat(c)))

type RBCol:
  RBRed{}
  RBBlk{}

type RBT:
  RBLeaf{}
  RBNode{c: RBCol, l: RBT, k: U32, r: RBT}

# Balance
# =======
#
# Okasaki's balance, split per side (only the side the insert descended
# into can hold the red-red violation), with one match per level.

# l = RBNode{RBRed, ll, lk, lr}, ll's root not red: check lr.
def rbt.balLB2(ll: RBT, lk: U32, lr: RBT, k: U32, r: RBT) -> RBT:
  match lr:
    case RBLeaf{}:
      RBNode{RBBlk{}, RBNode{RBRed{}, ll, lk, RBLeaf{}}, k, r}
    case RBNode{RBRed{}, b, y, cc}:
      RBNode{RBRed{}, RBNode{RBBlk{}, ll, lk, b}, y, RBNode{RBBlk{}, cc, k, r}}
    case RBNode{RBBlk{}, b, y, cc}:
      RBNode{RBBlk{}, RBNode{RBRed{}, ll, lk, RBNode{RBBlk{}, b, y, cc}}, k, r}

# parent is black: fix a red-red violation in the left child l.
def rbt.balLB(l: RBT, k: U32, r: RBT) -> RBT:
  match l:
    case RBLeaf{}:
      RBNode{RBBlk{}, RBLeaf{}, k, r}
    case RBNode{RBBlk{}, ll, lk, lr}:
      RBNode{RBBlk{}, RBNode{RBBlk{}, ll, lk, lr}, k, r}
    case RBNode{RBRed{}, RBLeaf{}, lk, lr}:
      rbt.balLB2(RBLeaf{}, lk, lr, k, r)
    case RBNode{RBRed{}, RBNode{RBRed{}, a, x, b}, lk, lr}:
      RBNode{RBRed{}, RBNode{RBBlk{}, a, x, b}, lk, RBNode{RBBlk{}, lr, k, r}}
    case RBNode{RBRed{}, RBNode{RBBlk{}, a, x, b}, lk, lr}:
      rbt.balLB2(RBNode{RBBlk{}, a, x, b}, lk, lr, k, r)

def rbt.balL(c: RBCol, l: RBT, k: U32, r: RBT) -> RBT:
  match c:
    case RBRed{}:
      RBNode{RBRed{}, l, k, r}
    case RBBlk{}:
      rbt.balLB(l, k, r)

# r = RBNode{RBRed, rl, rk, rr}, rl's root not red: check rr.
def rbt.balRB2(l: RBT, k: U32, rl: RBT, rk: U32, rr: RBT) -> RBT:
  match rr:
    case RBLeaf{}:
      RBNode{RBBlk{}, l, k, RBNode{RBRed{}, rl, rk, RBLeaf{}}}
    case RBNode{RBRed{}, cc, z, d}:
      RBNode{RBRed{}, RBNode{RBBlk{}, l, k, rl}, rk, RBNode{RBBlk{}, cc, z, d}}
    case RBNode{RBBlk{}, cc, z, d}:
      RBNode{RBBlk{}, l, k, RBNode{RBRed{}, rl, rk, RBNode{RBBlk{}, cc, z, d}}}

# parent is black: fix a red-red violation in the right child r.
def rbt.balRB(l: RBT, k: U32, r: RBT) -> RBT:
  match r:
    case RBLeaf{}:
      RBNode{RBBlk{}, l, k, RBLeaf{}}
    case RBNode{RBBlk{}, rl, rk, rr}:
      RBNode{RBBlk{}, l, k, RBNode{RBBlk{}, rl, rk, rr}}
    case RBNode{RBRed{}, RBLeaf{}, rk, rr}:
      rbt.balRB2(l, k, RBLeaf{}, rk, rr)
    case RBNode{RBRed{}, RBNode{RBRed{}, b, y, cc}, rk, rr}:
      RBNode{RBRed{}, RBNode{RBBlk{}, l, k, b}, y, RBNode{RBBlk{}, cc, rk, rr}}
    case RBNode{RBRed{}, RBNode{RBBlk{}, b, y, cc}, rk, rr}:
      rbt.balRB2(l, k, RBNode{RBBlk{}, b, y, cc}, rk, rr)

def rbt.balR(c: RBCol, l: RBT, k: U32, r: RBT) -> RBT:
  match c:
    case RBRed{}:
      RBNode{RBRed{}, l, k, r}
    case RBBlk{}:
      rbt.balRB(l, k, r)

# Insert
# ======

def rbt.ins(t: RBT, x: U32) -> RBT:
  match t:
    case RBLeaf{}:
      RBNode{RBRed{}, RBLeaf{}, x, RBLeaf{}}
    case RBNode{c, l, k, r}:
      ((x1, ex1), (x2, ex2)) = U32.copy(x)
      ((k1, ek1), (k2, ek2)) = U32.copy(k)
      match U32.cmp(x1, k1):
        case LT{}:
          rbt.balL(c, rbt.ins(l, x2), k2, r)
        case EQ{}:
          RBNode{c, l, k2, r}
        case GT{}:
          rbt.balR(c, l, k2, rbt.ins(r, x2))

def rbt.blacken(t: RBT) -> RBT:
  match t:
    case RBLeaf{}:
      RBLeaf{}
    case RBNode{c, l, k, r}:
      RBNode{RBBlk{}, l, k, r}

def rbt.insert(t: RBT, x: U32) -> RBT:
  rbt.blacken(rbt.ins(t, x))

# Checksum
# ========
#
# In-order rotating-add fold: fold(RBLeaf, h) = h;
# fold(RBNode{c,l,k,r}, h) = fold(r, mix(fold(l, h), k)).

def rbt.mix(h: U32, k: U32) -> U32:
  ((h1, e1), (h2, e2)) = U32.copy(h)
  U32.add(U32.or(U32.shln(1n, h1), U32.shrn(31n, h2)), k)

def rbt.fold(t: RBT, h: U32) -> U32:
  match t:
    case RBLeaf{}:
      h
    case RBNode{c, l, k, r}:
      rbt.fold(r, rbt.mix(rbt.fold(l, h), k))

# Driver
# ======

# insert keys next, next+1, ..., next+n-1
def bench.seq(n: Nat, next: U32, t: RBT) -> RBT:
  match n:
    case 0n:
      t
    case 1n+p:
      ((k, ek), (nx, en)) = U32.copy(next)
      bench.seq(p, U32.inc(nx), rbt.insert(t, k))

# p passes, each inserting keys 0..n-1
def bench.pass(p: Nat, n: Nat, t: RBT) -> RBT:
  match p:
    case 0n:
      t
    case 1n+q:
      ((n1, e1), (n2, e2)) = Nat.copy(n)
      bench.pass(q, n1, bench.seq(n2, U32.zero(), t))

# p passes of 2^k keys, then 2^a extras from 2^k and 2^b from 2^(k+1)
def rbt.bench(p: Nat, k: Nat, a: Nat, b: Nat) -> U32:
  ((k1, e1), (kr, e2)) = Nat.copy(k)
  ((k2, e3), (k3, e4)) = Nat.copy(kr)
  t1 = bench.pass(p, Nat.pow2(k1), RBLeaf{})
  t2 = bench.seq(Nat.pow2(a), U32.from_nat(Nat.pow2(k2)), t1)
  t3 = bench.seq(Nat.pow2(b), U32.from_nat(Nat.pow2(1n+k3)), t2)
  rbt.fold(t3, U32.zero())

def size.small() -> Nat & Nat & Nat & Nat:
  (3n, 6n, 3n, 2n)

# 4763
def expect.small() -> U32:
  u32d(0n, 4n, 667n)

def size.big() -> Nat & Nat & Nat & Nat:
  (19n, 18n, 15n, 14n)

# 3493273599
def expect.big() -> U32:
  u32d(3331n, 455n, 1023n)

def main() -> Bool:
  (p, k, a, b) = size.small()
  U32.is_eq(rbt.bench(p, k, a, b), expect.small())
