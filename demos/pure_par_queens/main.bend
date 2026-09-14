# Parallel N-queens: counts the ways to place n queens on an n x n
# board so that no two attack each other. Two phases share the work.
#
# 1. The fork tree. The first k = min(n, 4) rows are placed from an
#    index: each row takes w bits of it as its column, so the 2^(k*w)
#    indices name every k-row prefix (and some columns beyond the
#    board, which are never free). fork splits the index space in
#    halves with the parallel let `a b = f g` until one index is left.
#    Compiled, the leaves spread over every core as a balanced tree,
#    and their counts add up the tree.
#
# 2. The bitmask backtracker. A leaf decodes its prefix and, when every
#    prefix queen sits on a free column, fills the rows left one at a
#    time. Three words hold the attacks on the current row: cols has a
#    bit per taken column, ld and rd a bit per column that a left or a
#    right diagonal crosses. The row's free columns are one word,
#    full & ~(cols | ld | rd). solve peels its lowest bit, b = cand &
#    -cand, descends on the child row's words (cols | b, (ld | b) << 1,
#    (rd | b) >> 1), then goes on with the siblings cand - b. A row with
#    no free column keeps the count; a board with no row left adds one.
#
# solve's sibling loop shrinks a word, which the termination checker
# cannot see, so a Nat fuel rides ahead of every self-call. The fuel
# (left + 1)^2 exceeds the longest chain of calls: the j-th row from
# the bottom has at most j free columns and spends j + 1 calls.
#
# queens(n, w) takes the width w with 2^w >= n (the bits of a column).
# main calls queens!(8n, 3n): the `!` sends the call to the GPU when
# the machine has one, else to every CPU core; interpreted, the same
# tree runs sequentially.
#
# Run:
#   bend demos/pure_par_queens/main.bend                          (interprets)
#   bend demos/pure_par_queens/main.bend -o queens && ./queens    (the GPU, or every core)
#   ./queens --gpu off                                            (every core)
#   ./queens --gpu off --threads 1                                (one core)
#
# main counts the 8 x 8 board: 92. Compiled, queens!(12n, 4n) gives
# 14200, queens!(14n, 4n) 365596 and queens!(15n, 4n) 2279184.
import Base

# free
# ----
# the columns of a row that no placed queen attacks: full masks the
# board; cols, ld and rd are the columns and the two diagonals under
# attack on this row
def free(cols: U32, ld: U32, rd: U32, full: U32) -> U32:
  (full .&. U32.not(cols .|. ld .|. rd) : U32)

# solve
# -----
# the bitmask backtracker: one call owns one candidate word cand, the
# free columns of the current row (z = is_zero(cand), computed by the
# caller), with left rows to fill from this one on. It peels the lowest
# candidate, descends on the child row and then takes the siblings; the
# child's count rides into the sibling call as acc.
def solve(+fuel: Nat, +left: Nat, z: Bool, +cand: U32, +cols: U32, +ld: U32, +rd: U32, +full: U32, acc: U32) -> U32:
  match fuel left z:
    case 0n l z0:
      acc
    case 1n+g 0n z0:
      (acc + 1 : U32)
    case 1n+g 1n+p True{}:
      acc
    case 1n+g 1n+p False{}:
      +b = (cand .&. (0 - cand : U32) : U32)
      +c2 = (cols .|. b : U32)
      +l2 = ((ld .|. b) << 1n : U32)
      +r2 = ((rd .|. b) >> 1n : U32)
      +child = free(c2, l2, r2, full)
      +rest = (cand - b : U32)
      solve(g, 1n+p, U32.is_zero(rest), rest, cols, ld, rd, full,
        solve(g, p, U32.is_zero(child), child, c2, l2, r2, full, acc))

# prefix
# ------
# the first k rows from the index i: each row takes the low w bits of i
# as its column; ok says whether the last column placed was free (the
# caller tests it). When every prefix row is placed, solve fills the
# left rows; a column under attack ends the leaf with no count.
def prefix(k: Nat, ok: Bool, +w: Nat, +left: Nat, +i: U32, +cols: U32, +ld: U32, +rd: U32, +full: U32) -> U32:
  match k ok:
    case k0 False{}:
      0
    case 0n True{}:
      +cand = free(cols, ld, rd, full)
      solve(Nat.mul(1n+left, 1n+left), left, U32.is_zero(cand), cand, cols, ld, rd, full, 0)
    case 1n+q True{}:
      +b = (1 << U32.to_nat(i .&. ((1 << w) - 1 : U32)) : U32)
      prefix(q, U32.is_ne((b .&. free(cols, ld, rd, full) : U32), 0), w, left, (i >> w : U32),
        (cols .|. b : U32), ((ld .|. b) << 1n : U32), ((rd .|. b) >> 1n : U32), full)

# fork
# ----
# the prefix indices i .. i + 2^d - 1 as a balanced tree of forks: a
# leaf searches one prefix; a node forks its two halves and adds them
def fork(+d: Nat, +i: U32, +k: Nat, +w: Nat, +left: Nat, +full: U32) -> U32:
  match d:
    case 0n:
      prefix(k, True{}, w, left, i, 0, 0, 0, full)
    case 1n+p:
      a b = fork(p, i, k, w, left, full) fork(p, (i + (1 << p) : U32), k, w, left, full)
      (a + b : U32)

# queens
# ------
# the solution count of the n x n board: k = min(n, 4) prefix rows of w
# bits each make a fork tree of depth k * w; the board mask full has
# the low n bits set
def queens(+n: Nat, +w: Nat) -> U32:
  +left = Nat.sub(n, 4n)
  +k = Nat.sub(n, left)
  fork(Nat.mul(k, w), 0, k, w, left, ((1 << n) - 1 : U32))

def main() -> U32:
  queens!(8n, 3n)
