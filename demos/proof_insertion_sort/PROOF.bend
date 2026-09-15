# proof_insertion_sort: the proofs. This file imports the program (as
# Sort) and the claims (as Laws) and fills every law as def
# Laws.<name>. Each law is proved by induction on the list: the Nil
# case is conversion, the cons case rewrites with the induction
# hypothesis (the structural self-call) and with a lemma about insert.
# The last two sections add the fixed-point law (a sorted list is a
# fixed point of sort, so sort is idempotent) and the minimum law (the
# head of sort's output bounds the whole input).
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

# Fixed point
# -----------
# insert(x, h <> t) is dec(x, h, t, insert(x, t), le_case(x, h)): on a
# proof e of x <= h the verdict computes to OL{e} (le_case_ol, by
# induction on the two numbers), and dec puts x at the head. So a
# sorted list ascending from lo is a fixed point of sort: the tail is
# one by the induction hypothesis, and inserting the head into it
# puts the head back in front.

law le_case_ol:
  for x : Nat
  for h : Nat
  for e : Sort.LE(x, h)
  {Sort.OL{e} == Sort.le_case(x, h) : Sort.LEOr<x, h>}

def le_case_ol(x, h, e):
  match x h:
    case 0n 0n:
      match e:
        case Unit{}:
          {==}
    case 0n 1n+b:
      match e:
        case Unit{}:
          {==}
    case 1n+a 0n:
      match e:
    case 1n+a 1n+b:
      %le_case_ol(a, b, e) : {Sort.OL{e} == Sort.le_case.fin(a, b, _) : Sort.LEOr<1n+a, 1n+b>}
      {==}

law insert_head:
  for +x : Nat
  for  h : Nat
  for -t : List<&2, Nat>
  for  e : Sort.LE(x, h)
  {x <> h <> t == Sort.insert(x, h <> t) : List<&2, Nat>}

def insert_head(x, h, t, e):
  %le_case_ol(x, h, e) : {x <> h <> t == Sort.dec(x, h, t, Sort.insert(x, t), _) : List<&2, Nat>}
  {==}

def Laws.sort_fixed(xs, lo, s):
  match xs:
    case Nil{}:
      {==}
    case h <> Nil{}:
      {==}
    case h <> h2 <> t2:
      (lh, (e, st)) = s
      +e2 = e
      %Laws.sort_fixed(h2 <> t2, h, (e2, st)) : {h <> h2 <> t2 == Sort.insert(h, _) : List<&2, Nat>}
      insert_head(h, h2, t2, e2)

# sort(xs) is sorted, so it is a fixed point of sort
def Laws.sort_idem(xs):
  Equal.sym(List<&2, Nat>, Sort.sort(xs), Sort.sort(Sort.sort(xs)), Laws.sort_fixed(Sort.sort(xs), 0n, Laws.sort_sorted(xs)))

# Minimum
# -------
# Below(lo, xs) says lo is at most every element of xs. The argument:
# sort(xs) is sorted, so its head m is below all of sort(xs)
# (sorted_below, through the transitivity of LE); and a bound of
# sort(xs) is a bound of xs (below_sort), because a bound of
# insert(x, ys) bounds x and ys (below_ins, the usual .fin induction
# on the verdict).

law le_refl:
  for a: Nat
  Sort.LE(a, a)

def le_refl(a):
  match a:
    case 0n:
      Unit{}
    case 1n+p:
      le_refl(p)

law le_trans:
  for a  : Nat
  for b  : Nat
  for c  : Nat
  for ab : Sort.LE(a, b)
  for bc : Sort.LE(b, c)
  Sort.LE(a, c)

def le_trans(a, b, c, ab, bc):
  match a b c:
    case 0n _ _:
      Unit{}
    case 1n+a1 0n _:
      match ab:
    case 1n+a1 1n+b1 0n:
      match bc:
    case 1n+a1 1n+b1 1n+c1:
      le_trans(a1, b1, c1, ab, bc)

# a list ascending from lo is bounded by any lo' <= lo
law sorted_below:
  for +xs : List<&2, Nat>
  for +lo2: Nat
  for +lo : Nat
  for  l  : Sort.LE(lo2, lo)
  for  s  : Sort.Sorted.from(lo, xs)
  Sort.Below(lo2, xs)

def sorted_below(xs, lo2, lo, l, s):
  match xs:
    case Nil{}:
      Unit{}
    case h <> t:
      (lh, st) = s
      +lh2 = le_trans(lo2, lo, h, l, lh)
      (lh2, sorted_below(t, lo2, h, lh2, st))

# a bound of insert(x, ys) bounds x and ys
law below_ins.fin:
  for -lo : Nat
  for -x  : Nat
  for -h  : Nat
  for -t  : List<&2, Nat>
  for rec : Sort.Below(lo, Sort.insert(x, t)) -> (Sort.LE(lo, x) & Sort.Below(lo, t))
  for c   : Sort.LEOr<x, h>
  for b   : Sort.Below(lo, Sort.dec(x, h, t, Sort.insert(x, t), c))
  (Sort.LE(lo, x) & Sort.Below(lo, h <> t))

def below_ins.og(-lo: Nat, -x: Nat, -h: Nat, -t: List<&2, Nat>, lh: Sort.LE(lo, h), p: Sort.LE(lo, x) & Sort.Below(lo, t)) -> (Sort.LE(lo, x) & Sort.Below(lo, h <> t)):
  (lx, bt) = p
  (lx, (lh, bt))

def below_ins.fin(lo, x, h, t, rec, c, b):
  match c:
    case Sort.OL{e}:
      b
    case Sort.OG{e}:
      (lh, bi) = b
      below_ins.og(lo, x, h, t, lh, rec(bi))

law below_ins:
  for  ys : List<&2, Nat>
  for -lo : Nat
  for +x  : Nat
  for  b  : Sort.Below(lo, Sort.insert(x, ys))
  (Sort.LE(lo, x) & Sort.Below(lo, ys))

def below_ins(ys, lo, x, b):
  match ys:
    case Nil{}:
      b
    case h <> t:
      below_ins.fin(lo, x, h, t, bi => below_ins(t, lo, x, bi), Sort.le_case(x, h), b)

# a bound of sort(xs) is a bound of xs
def below_sort.step(-lo: Nat, -h: Nat, -t: List<&2, Nat>, p: Sort.LE(lo, h) & Sort.Below(lo, Sort.sort(t)), rec: Sort.Below(lo, Sort.sort(t)) -> Sort.Below(lo, t)) -> Sort.Below(lo, h <> t):
  (lh, bs) = p
  (lh, rec(bs))

law below_sort:
  for +xs : List<&2, Nat>
  for -lo : Nat
  for  b  : Sort.Below(lo, Sort.sort(xs))
  Sort.Below(lo, xs)

def below_sort(xs, lo, b):
  match xs:
    case Nil{}:
      b
    case h <> t:
      below_sort.step(lo, h, t, below_ins(Sort.sort(t), lo, h, b), bs => below_sort(t, lo, bs))

# the head of a sorted list is below the whole list
def head_below(+m: Nat, t: List<&2, Nat>, s: Sort.Sorted(m <> t)) -> Sort.Below(m, m <> t):
  (l0, st) = s
  +r = le_refl(m)
  (r, sorted_below(t, m, m, r, st))

# sort(xs) is sorted; it is m <> t, so m bounds it, and so bounds xs
def sort_min.go(+m: Nat, t: List<&2, Nat>, -xs: List<&2, Nat>, e: {m <> t == Sort.sort(xs) : List<&2, Nat>}) -> (Sort.Sorted(Sort.sort(xs)) -> Sort.Below(m, Sort.sort(xs))):
  %e : (Sort.Sorted(_) -> Sort.Below(m, _))
  s => head_below(m, t, s)

def Laws.sort_min(m, t, xs, e):
  below_sort(xs, m, sort_min.go(m, t, xs, e)(Laws.sort_sorted(xs)))
