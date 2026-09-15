# Parallel N-queens: counts the ways to place n queens on an n x n
# board so that no two attack each other. A board is the list of the
# chosen columns, one per row, the last row placed first; a column is
# free when no queen already placed shares it or a diagonal with it.
# Two phases share the work.
#
# 1. The fork tree. fork splits the first row's columns 0 .. 2^d - 1
#    in halves with the parallel let `a b = f g` until one column is
#    left; a leaf places its queen (when the column is on the board)
#    and fills the rows left. Compiled, the leaves spread over every
#    core as a balanced tree, and their boards join up the tree.
#
# 2. The frontier search. solve fills one row at a time: grow_all
#    extends every board of the frontier by every free column, and
#    the boards that survive all rows are the solutions.
#
# queens(n, d) takes the depth d with 2^d >= n. main calls
# queens!(8n, 3n): the `!` sends the call to the GPU when the machine
# has one, else to every CPU core; interpreted, the same tree runs
# sequentially.
#
# Run:
#   bend demos/pure_par_queens/main.bend                          (interprets)
#   bend demos/pure_par_queens/main.bend -o queens && ./queens    (the GPU, or every core)
#   ./queens --gpu off                                            (every core)
#   ./queens --gpu off --threads 1                                (one core)
#
# main counts the 8 x 8 board: 92.
import Base

# Numbers
# -------

def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n+p:
      1n+add(p, b)

def pow2(d: Nat) -> Nat:
  match d:
    case 0n:
      1n
    case 1n+p:
      +h = pow2(p)
      add(h, h)

def eqn(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True{}
    case 0n 1n+bp:
      False{}
    case 1n+ap 0n:
      False{}
    case 1n+ap 1n+bp:
      eqn(ap, bp)

def ltn(a: Nat, b: Nat) -> Bool:
  match a b:
    case a0 0n:
      False{}
    case 0n 1n+bp:
      True{}
    case 1n+ap 1n+bp:
      ltn(ap, bp)

# Boards
# ------

# the columns 0 .. n - 1
def cols(n: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      []
    case 1n++p:
      p <> cols(p)

# ok(c, qs, k): no queen of qs shares a column or a diagonal with a
# queen at column c, k rows below the first of qs
def ok(+c: Nat, +qs: List<&2, Nat>, +k: Nat) -> Bool:
  match qs:
    case []:
      True{}
    case q <> rest:
      Bool.not(eqn(c, q) || eqn(c, add(q, k)) || eqn(add(c, k), q)) && ok(c, rest, 1n+k)

# column c is free on the row after the board qs
def free(+c: Nat, +qs: List<&2, Nat>) -> Bool:
  ok(c, qs, 1n)

def cat(xs: List<&2, List<&2, Nat>>, ys: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match xs:
    case []:
      ys
    case q <> t:
      q <> cat(t, ys)

# Search
# ------

# the board qs grown by column c when c is free (the verdict b)
def pick(b: Bool, c: Nat, qs: List<&2, Nat>) -> List<&2, List<&2, Nat>>:
  match b:
    case True{}:
      [c <> qs]
    case False{}:
      []

# the board qs grown by each free column of cs
def grow_one(+cs: List<&2, Nat>, +qs: List<&2, Nat>) -> List<&2, List<&2, Nat>>:
  match cs:
    case []:
      []
    case c <> rest:
      cat(pick(free(c, qs), c, qs), grow_one(rest, qs))

# every board of the frontier bs grown by one row
def grow_all(+n: Nat, +bs: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match bs:
    case []:
      []
    case qs <> rest:
      cat(grow_one(cols(n), qs), grow_all(n, rest))

# the frontier bs grown by rows rows
def solve(rows: Nat, +n: Nat, bs: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match rows:
    case 0n:
      bs
    case 1n+r:
      solve(r, n, grow_all(n, bs))

# the boards with the first queen at column i, when i is on the board
def first(b: Bool, i: Nat) -> List<&2, List<&2, Nat>>:
  match b:
    case True{}:
      [[i]]
    case False{}:
      []

# a leaf: the first queen at column i, then r rows filled
def leaf(+i: Nat, r: Nat, +n: Nat) -> List<&2, List<&2, Nat>>:
  solve(r, n, first(ltn(i, n), i))

# the first-row columns i .. i + 2^d - 1 as a balanced tree of forks:
# a node forks its two halves and joins their boards
def fork(+d: Nat, +i: Nat, +r: Nat, +n: Nat) -> List<&2, List<&2, Nat>>:
  match d:
    case 0n:
      leaf(i, r, n)
    case 1n++p:
      a b = fork(p, i, r, n) fork(p, add(pow2(p), i), r, n)
      cat(a, b)

# the solutions of the n x n board, found by a fork tree of depth d
def boards(n: Nat, d: Nat) -> List<&2, List<&2, Nat>>:
  match n:
    case 0n:
      [[]]
    case 1n++r:
      fork(d, 0n, r, 1n+r)

def length(bs: List<&2, List<&2, Nat>>) -> Nat:
  match bs:
    case []:
      0n
    case q <> t:
      1n+length(t)

def queens(n: Nat, d: Nat) -> Nat:
  length(boards(n, d))

# Spec
# ----

# a board is safe when every queen is free on the board below it
def safe(+qs: List<&2, Nat>) -> Bool:
  match qs:
    case []:
      True{}
    case q <> rest:
      free(q, rest) && safe(rest)

def all_safe(bs: List<&2, List<&2, Nat>>) -> Bool:
  match bs:
    case []:
      True{}
    case qs <> rest:
      safe(qs) && all_safe(rest)

# the sequential meaning of the fork tree: the leaves i .. i + k - 1
# one after the other
def flat(k: Nat, +i: Nat, +r: Nat, +n: Nat) -> List<&2, List<&2, Nat>>:
  match k:
    case 0n:
      []
    case 1n+m:
      cat(leaf(i, r, n), flat(m, 1n+i, r, n))

# Main
# ----

def main() -> Nat:
  queens!(8n, 3n)
