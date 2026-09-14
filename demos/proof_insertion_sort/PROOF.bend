# proof_insertion_sort: the proofs. This file imports the program (as
# Sort) and the claims (as Laws) and fills every law as def
# Laws.<name>. Each law is proved by induction on the list: the Nil
# case is conversion, the cons case rewrites with the induction
# hypothesis (the structural self-call) and with a lemma about insert.
#
# Every insert lemma has the same shape. insert(x, h <> t) is
# dec(x, h, t, insert(x, t), le_case(x, h)), and on an open x and h
# the verdict le_case(x, h) is stuck. So a .fin helper takes the
# verdict c as a parameter and matches it: each arm specializes dec,
# and the induction hypothesis arrives as the parameter rec, computed
# by the self-call at the caller. The affine core prices the double
# uses: a value used twice rides a + binder (Nat and List<&2, Nat> are
# Data), and a parameter used only in types is dead (-).

import Base
import ./main.bend as Sort
import ./LAWS.bend as Laws

# Sortedness
# ----------
# Sorted.from(lo, xs) carries the lower bound lo, so inserting x into
# a list bounded by lo keeps the bound when lo <= x: in the OL arm x
# heads the result and the old bound proof lh moves under it; in the
# OG arm h stays the head and the recursion inserts x into t under
# the bound h, which the verdict's evidence e supplies.

law sorted_ins.fin:
  for -lo : Nat
  for -x  : Nat
  for -h  : Nat
  for -t  : List<&2, Nat>
  for sx  : Sort.Sorted.from(lo, h <> t)
  for lx  : Sort.LE(lo, x)
  for rec : (Sort.Sorted.from(h, t) -> Sort.LE(h, x) -> Sort.Sorted.from(h, Sort.insert(x, t)))
  for c   : Sort.LEOr<x, h>
  Sort.Sorted.from(lo, Sort.dec(x, h, t, Sort.insert(x, t), c))

def sorted_ins.fin(lo, x, h, t, sx, lx, rec, c):
  (lh, st) = sx
  match c:
    case Sort.OL{e}:
      (lx, e, st)
    case Sort.OG{e}:
      (lh, rec(st, e))

law sorted_ins:
  for xs  : List<&2, Nat>
  for -lo : Nat
  for +x  : Nat
  Sort.Sorted.from(lo, xs) -> Sort.LE(lo, x) -> Sort.Sorted.from(lo, Sort.insert(x, xs))

def sorted_ins(xs, lo, x):
  match xs:
    case Nil{}:
      sx => lx => (lx, Unit{})
    case h <> t:
      sx => lx => sorted_ins.fin(lo, x, h, t, sx, lx, sorted_ins(t, h, x), Sort.le_case(x, h))

# sort(h <> t) inserts h into the sorted sort(t); 0n bounds everything
def Laws.sort_sorted(xs):
  match xs:
    case Nil{}:
      Unit{}
    case h <> t:
      sorted_ins(Sort.sort(t), 0n, h)(Laws.sort_sorted(t), Unit{})

# Permutation
# -----------
# count(x, y <> ys) is bump(eq(x, y), count(x, ys)). insert moves y
# past the heads it exceeds; bump_swap moves y's bump past theirs.

law bump_swap:
  for  a: Bool
  for  b: Bool
  for -n: Nat
  {Sort.bump(a, Sort.bump(b, n)) == Sort.bump(b, Sort.bump(a, n)) : Nat}

def bump_swap(a, b, n):
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# inserting y into xs adds y's bump to every count, as consing y does:
# stated with the insert on the right, the side the law eliminates
law count_ins.fin:
  for +x  : Nat
  for  y  : Nat
  for  h  : Nat
  for -t  : List<&2, Nat>
  for rec : {Sort.count(x, y <> t) == Sort.count(x, Sort.insert(y, t)) : Nat}
  for c   : Sort.LEOr<y, h>
  {Sort.count(x, y <> h <> t) == Sort.count(x, Sort.dec(y, h, t, Sort.insert(y, t), c)) : Nat}

def count_ins.fin(x, y, h, t, rec, c):
  match c:
    case Sort.OL{e}:
      {==}
    case Sort.OG{e}:
      %rec : {Sort.count(x, y <> h <> t) == Sort.bump(Sort.eq(x, h), _) : Nat}
      bump_swap(Sort.eq(x, y), Sort.eq(x, h), Sort.count(x, t))

law count_ins:
  for +x  : Nat
  for +y  : Nat
  for +xs : List<&2, Nat>
  {Sort.count(x, y <> xs) == Sort.count(x, Sort.insert(y, xs)) : Nat}

def count_ins(x, y, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      count_ins.fin(x, y, h, t, count_ins(x, y, t), Sort.le_case(y, h))

# count(x, sort(h <> t)) is count(x, insert(h, sort(t))): count_ins
# turns it into count(x, h <> sort(t)), and the IH closes the tail
def Laws.sort_perm(x, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %count_ins(x, h, Sort.sort(t)) : {_ == Sort.bump(Sort.eq(x, h), Sort.count(x, t)) : Nat}
      %Laws.sort_perm(x, t) : {Sort.bump(Sort.eq(x, h), Sort.count(x, Sort.sort(t))) == Sort.bump(Sort.eq(x, h), _) : Nat}
      {==}

# Length
# ------
# the same induction with a simpler lemma: insert adds one to the length

law len_ins.fin:
  for -x  : Nat
  for -h  : Nat
  for -t  : List<&2, Nat>
  for rec : {1n+Sort.length(t) == Sort.length(Sort.insert(x, t)) : Nat}
  for c   : Sort.LEOr<x, h>
  {1n+Sort.length(h <> t) == Sort.length(Sort.dec(x, h, t, Sort.insert(x, t), c)) : Nat}

def len_ins.fin(x, h, t, rec, c):
  match c:
    case Sort.OL{e}:
      {==}
    case Sort.OG{e}:
      %rec : {2n+Sort.length(t) == 1n+_ : Nat}
      {==}

law len_ins:
  for +x : Nat
  for xs : List<&2, Nat>
  {1n+Sort.length(xs) == Sort.length(Sort.insert(x, xs)) : Nat}

def len_ins(x, xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      len_ins.fin(x, h, t, len_ins(x, t), Sort.le_case(x, h))

def Laws.sort_length(xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %len_ins(h, Sort.sort(t)) : {_ == 1n+Sort.length(t) : Nat}
      %Laws.sort_length(t) : {1n+Sort.length(Sort.sort(t)) == 1n+_ : Nat}
      {==}
