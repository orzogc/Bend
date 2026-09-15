# Parallel N-queens -- the proofs. This file imports the program (as
# Q) and the claims (as Laws) and fills every law.
#
# Soundness is an invariant of the frontier: a frontier of safe boards
# grows into a frontier of safe boards, since a board grows only by a
# column that free says is free, and safe(c <> qs) is exactly
# free(c, qs) && safe(qs). The tower climbs the program: pick_safe
# (one column, deciding the verdict with the Bool-inspect idiom: the
# goal abstracted over b with {b == free(c, qs)} to spend), grow_one
# (one board), grow_all (one row), solve (all rows), then the fork
# tree by induction on its depth, with all_safe_cat to split a join.
#
# The parallel-equals-sequential law is an induction on the depth:
# flat_add splits a flat loop over m + n columns in two, and the
# recursive call is the induction hypothesis on each half.
import Base
import ./main.bend as Q
import ./LAWS.bend as Laws

# Booleans
# --------

# BD(b, t, f) picks a type by a Bool, so a rewrite through it refutes
# a clash between True{} and False{}
def BD(b: Bool, tc: Type, fc: Type) -> Type:
  match b:
    case True{}:
      tc
    case False{}:
      fc

def and_assoc(a: Bool, -b: Bool, -c: Bool) -> {(a && b) && c == a && (b && c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def and_l(a: Bool, -b: Bool, e: {True{} == a && b : Bool}) -> {True{} == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      %e : BD(_, Unit, {True{} == False{} : Bool})
      Unit{}

def and_r(a: Bool, -b: Bool, e: {True{} == a && b : Bool}) -> {True{} == b : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      %e : BD(_, Unit, {True{} == b : Bool})
      Unit{}

# Lists of boards
# ---------------

def cat_nil(xs: List<&2, List<&2, Nat>>) -> {xs == Q.cat(xs, []) : List<&2, List<&2, Nat>>}:
  match xs:
    case []:
      {==}
    case q <> t:
      %cat_nil(t) : {q <> t == q <> _ : List<&2, List<&2, Nat>>}
      {==}

def cat_assoc(xs: List<&2, List<&2, Nat>>, -ys: List<&2, List<&2, Nat>>, -zs: List<&2, List<&2, Nat>>)
  -> {Q.cat(xs, Q.cat(ys, zs)) == Q.cat(Q.cat(xs, ys), zs) : List<&2, List<&2, Nat>>}:
  match xs:
    case []:
      {==}
    case q <> t:
      %cat_assoc(t, ys, zs) : {q <> Q.cat(t, Q.cat(ys, zs)) == q <> _ : List<&2, List<&2, Nat>>}
      {==}

# a join is safe when both halves are
def all_safe_cat(xs: List<&2, List<&2, Nat>>, -ys: List<&2, List<&2, Nat>>)
  -> {Q.all_safe(xs) && Q.all_safe(ys) == Q.all_safe(Q.cat(xs, ys)) : Bool}:
  match xs:
    case []:
      {==}
    case q <> t:
      %all_safe_cat(t, ys) : {(Q.safe(q) && Q.all_safe(t)) && Q.all_safe(ys) == Q.safe(q) && _ : Bool}
      %and_assoc(Q.safe(q), Q.all_safe(t), Q.all_safe(ys)) : {(Q.safe(q) && Q.all_safe(t)) && Q.all_safe(ys) == _ : Bool}
      {==}

# Soundness
# ---------

# a safe board grown by a column the verdict b admits stays safe
def pick_safe(+c: Nat, +qs: List<&2, Nat>, hq: {True{} == Q.safe(qs) : Bool}, b: Bool, e: {b == Q.free(c, qs) : Bool})
  -> {True{} == Q.all_safe(Q.pick(b, c, qs)) : Bool}:
  match b:
    case True{}:
      %e : {True{} == (_ && Q.safe(qs)) && True{} : Bool}
      %hq : {True{} == _ && True{} : Bool}
      {==}
    case False{}:
      {==}

def grow_one_safe(+cs: List<&2, Nat>, +qs: List<&2, Nat>, +hq: {True{} == Q.safe(qs) : Bool})
  -> {True{} == Q.all_safe(Q.grow_one(cs, qs)) : Bool}:
  match cs:
    case []:
      {==}
    case c <> rest:
      %all_safe_cat(Q.pick(Q.free(c, qs), c, qs), Q.grow_one(rest, qs)) : {True{} == _ : Bool}
      %pick_safe(c, qs, hq, Q.free(c, qs), {==}) : {True{} == _ && Q.all_safe(Q.grow_one(rest, qs)) : Bool}
      %grow_one_safe(rest, qs, hq) : {True{} == True{} && _ : Bool}
      {==}

def grow_all_safe(+n: Nat, +bs: List<&2, List<&2, Nat>>, +h: {True{} == Q.all_safe(bs) : Bool})
  -> {True{} == Q.all_safe(Q.grow_all(n, bs)) : Bool}:
  match bs:
    case []:
      {==}
    case qs <> rest:
      %all_safe_cat(Q.grow_one(Q.cols(n), qs), Q.grow_all(n, rest)) : {True{} == _ : Bool}
      %grow_one_safe(Q.cols(n), qs, and_l(Q.safe(qs), Q.all_safe(rest), h)) : {True{} == _ && Q.all_safe(Q.grow_all(n, rest)) : Bool}
      %grow_all_safe(n, rest, and_r(Q.safe(qs), Q.all_safe(rest), h)) : {True{} == True{} && _ : Bool}
      {==}

# the invariant: a safe frontier stays safe through every row
def solve_safe(rows: Nat, +n: Nat, +bs: List<&2, List<&2, Nat>>, h: {True{} == Q.all_safe(bs) : Bool})
  -> {True{} == Q.all_safe(Q.solve(rows, n, bs)) : Bool}:
  match rows:
    case 0n:
      h
    case 1n+r:
      solve_safe(r, n, Q.grow_all(n, bs), grow_all_safe(n, bs, h))

# one queen is always safe, whether or not its column is on the board
def first_safe(b: Bool, -i: Nat) -> {True{} == Q.all_safe(Q.first(b, i)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a leaf starts from one safe queen and runs the invariant; a node
# joins two safe halves, each the induction hypothesis
def Laws.fork_safe(d, i, r, n):
  match d:
    case 0n:
      solve_safe(r, n, Q.first(Q.ltn(i, n), i), first_safe(Q.ltn(i, n), i))
    case 1n++p:
      %all_safe_cat(Q.fork(p, i, r, n), Q.fork(p, Q.add(Q.pow2(p), i), r, n)) : {True{} == _ : Bool}
      %Laws.fork_safe(p, i, r, n) : {True{} == _ && Q.all_safe(Q.fork(p, Q.add(Q.pow2(p), i), r, n)) : Bool}
      %Laws.fork_safe(p, Q.add(Q.pow2(p), i), r, n) : {True{} == True{} && _ : Bool}
      {==}

def Laws.boards_safe(n, d):
  match n:
    case 0n:
      {==}
    case 1n++r:
      Laws.fork_safe(d, 0n, r, 1n+r)

# Parallel equals sequential
# --------------------------

def add_succ(a: Nat, -b: Nat) -> {1n+Q.add(a, b) == Q.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {2n+Q.add(p, b) == 1n+_ : Nat}
      {==}

# a flat loop over m + k columns is the loop over the first m, then
# the loop over the next k from where the first stopped
def flat_add(m: Nat, k: Nat, +i: Nat, +r: Nat, +n: Nat)
  -> {Q.cat(Q.flat(m, i, r, n), Q.flat(k, Q.add(m, i), r, n)) == Q.flat(Q.add(m, k), i, r, n) : List<&2, List<&2, Nat>>}:
  match m:
    case 0n:
      {==}
    case 1n++q:
      %flat_add(q, k, 1n+i, r, n) : {Q.cat(Q.cat(Q.leaf(i, r, n), Q.flat(q, 1n+i, r, n)), Q.flat(k, 1n+Q.add(q, i), r, n)) == Q.cat(Q.leaf(i, r, n), _) : List<&2, List<&2, Nat>>}
      %add_succ(q, i) : {Q.cat(Q.cat(Q.leaf(i, r, n), Q.flat(q, 1n+i, r, n)), Q.flat(k, 1n+Q.add(q, i), r, n)) == Q.cat(Q.leaf(i, r, n), Q.cat(Q.flat(q, 1n+i, r, n), Q.flat(k, _, r, n))) : List<&2, List<&2, Nat>>}
      %cat_assoc(Q.leaf(i, r, n), Q.flat(q, 1n+i, r, n), Q.flat(k, 1n+Q.add(q, i), r, n)) : {_ == Q.cat(Q.leaf(i, r, n), Q.cat(Q.flat(q, 1n+i, r, n), Q.flat(k, 1n+Q.add(q, i), r, n))) : List<&2, List<&2, Nat>>}
      {==}

# a leaf is the loop over one column; a node is the loop over
# 2^p + 2^p columns, split by flat_add into the two halves, each the
# induction hypothesis
def Laws.fork_is_flat(d, i, r, n):
  match d:
    case 0n:
      cat_nil(Q.leaf(i, r, n))
    case 1n++p:
      %flat_add(Q.pow2(p), Q.pow2(p), i, r, n) : {Q.cat(Q.fork(p, i, r, n), Q.fork(p, Q.add(Q.pow2(p), i), r, n)) == _ : List<&2, List<&2, Nat>>}
      %Laws.fork_is_flat(p, i, r, n) : {Q.cat(Q.fork(p, i, r, n), Q.fork(p, Q.add(Q.pow2(p), i), r, n)) == Q.cat(_, Q.flat(Q.pow2(p), Q.add(Q.pow2(p), i), r, n)) : List<&2, List<&2, Nat>>}
      %Laws.fork_is_flat(p, Q.add(Q.pow2(p), i), r, n) : {Q.cat(Q.fork(p, i, r, n), Q.fork(p, Q.add(Q.pow2(p), i), r, n)) == Q.cat(Q.fork(p, i, r, n), _) : List<&2, List<&2, Nat>>}
      {==}

def Laws.counts():
  ({==}, {==}, {==})
