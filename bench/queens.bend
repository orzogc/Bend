#[halts]
import Base
# queens: exhaustive N-queens backtracking search, ported from Bend3's
# par_queens (fork/batch prefix machinery dropped: no parallelism in
# Bend yet, so the full recursive solver runs from the root). The
# classic bitmask backtracker: peel the lowest candidate bit
# b = cand & (0 - cand), descend on the child row's candidate word
# full & ~(nc|nl|nr), then continue on the sibling set cand - b;
# Stats{sols, nodes} counts one node per peel.
# Checksum = (sols * 2654435761) ^ nodes.
# Needs #[halts]: the solver recurses on the shrinking candidate word,
# which is not structural.
#
# Sizes: small n = 4 (sols 2, nodes 16, expect 1013904242), big n = 8
# (sols 92, nodes 2056, expect 3689919380; size 5 gives 774553823).

type Stats:
  MkStats{sols: U32, nodes: U32}

# u32 constant from base-2^10 digits: a*2^20 + b*2^10 + c
def u32d(a: Nat, b: Nat, c: Nat) -> U32:
  U32.add(U32.shln(20n, U32.from_nat(a)), U32.add(U32.shln(10n, U32.from_nat(b)), U32.from_nat(c)))

# lowest set bit: c & (0 - c); U32.sub wraps mod 2^32
def lowbit(c: U32) -> U32:
  ((c1, e1), (c2, e2)) = U32.copy(c)
  U32.and(c1, U32.sub(U32.zero(), c2))

# Knuth's 2654435761 = 2*2^30 + 483*2^20 + 478*2^10 + 433
def magic() -> U32:
  U32.add(U32.shln(30n, U32.from_nat(2n)), u32d(483n, 478n, 433n))

# the classic bitmask backtracker: descend on the child candidate
# word (the natural non-tail call), then tail-loop on the sibling set
def solve(cand: U32, cols: U32, ld: U32, rd: U32, full: U32, sols: U32, nodes: U32) -> Stats:
  ((ca, e1), (cb, e2)) = U32.copy(cand)
  match U32.is_zero(ca):
    case True{}:
      MkStats{sols, nodes}
    case False{}:
      ((cc, e3), (cd, e4)) = U32.copy(cb)
      ((b1, e5), (b2, e6)) = U32.copy(lowbit(cc))
      ((col1, e7), (col2, e8)) = U32.copy(cols)
      ((nc1, e9), (nc2, e10)) = U32.copy(U32.or(col1, b1))
      ((f1, e11), (f2, e12)) = U32.copy(full)
      match U32.is_eq(nc1, f1):
        case True{}:
          solve(U32.sub(cd, b2), col2, ld, rd, f2, U32.inc(sols), U32.inc(nodes))
        case False{}:
          ((b3, e13), (b4, e14)) = U32.copy(b2)
          ((b5, e15), (b6, e16)) = U32.copy(b3)
          ((l1, e17), (l2, e18)) = U32.copy(ld)
          ((r1, e19), (r2, e20)) = U32.copy(rd)
          ((f3, e21), (f4, e22)) = U32.copy(f2)
          ((f5, e23), (f6, e24)) = U32.copy(f3)
          ((nl1, e25), (nl2, e26)) = U32.copy(U32.shl(U32.or(l1, b5)))
          ((nr1, e27), (nr2, e28)) = U32.copy(U32.shr(U32.or(r1, b6)))
          ((nc3, e29), (nc4, e30)) = U32.copy(nc2)
          match solve(U32.and(f5, U32.not(U32.or(nc3, U32.or(nl1, nr1)))), nc4, nl2, nr2, f6, sols, U32.inc(nodes)):
            case MkStats{s1, n1}:
              solve(U32.sub(cd, b4), col2, l2, r2, f4, s1, n1)

# run the solver from the root: cand = full = (1 << n) - 1
def queens(n: Nat) -> Stats:
  ((fa, e1), (fb, e2)) = U32.copy(U32.sub(U32.shln(n, U32.one()), U32.one()))
  solve(fa, U32.zero(), U32.zero(), U32.zero(), fb, U32.zero(), U32.zero())

def checksum(st: Stats) -> U32:
  match st:
    case MkStats{s, w}:
      U32.xor(U32.mul(s, magic()), w)

def size.small() -> Nat:
  4n

def expect.small() -> U32:
  u32d(966n, 956n, 882n)

def size.big() -> Nat:
  8n

def expect.big() -> U32:
  U32.add(U32.shln(30n, U32.from_nat(3n)), u32d(446n, 1004n, 916n))

def main() -> Bool:
  U32.is_eq(checksum(queens(size.small())), expect.small())
