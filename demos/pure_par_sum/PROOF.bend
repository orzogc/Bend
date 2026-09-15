# Parallel sum -- the proofs. This file imports the program (as Par)
# and the claims (as Laws) and fills every law. Both tree laws are
# inductions on the depth: a leaf is one number, and a node's match on
# 1n+p unfolds the fork into add(tree(p, i), tree(p, jump(p, i))), so
# the recursive call is the induction hypothesis on each half. The
# loop side needs seq_add, which splits a loop over m + n numbers into
# two loops, and the add lemmas that move a successor and reassociate.
# A rewrite %e : P spends e : {x == y} once, turning the goal P(y) into
# P(x), so every lemma is stated with the term its callers eliminate on
# the right.
import Base
import ./main.bend as Par
import ./LAWS.bend as Laws

# Addition
# --------

def add_zero(a: Nat) -> {a == Par.add(a, 0n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+p == 1n+_ : Nat}
      {==}

def add_succ(a: Nat, -b: Nat) -> {1n+Par.add(a, b) == Par.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {2n+Par.add(p, b) == 1n+_ : Nat}
      {==}

def add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Par.add(a, Par.add(b, c)) == Par.add(Par.add(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Par.add(p, Par.add(b, c)) == 1n+_ : Nat}
      {==}

def add_swap(x: Nat, +y: Nat, +z: Nat) -> {Par.add(x, Par.add(y, z)) == Par.add(y, Par.add(x, z)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+q:
      %add_succ(y, Par.add(q, z)) : {1n+Par.add(q, Par.add(y, z)) == _ : Nat}
      %add_swap(q, y, z) : {1n+Par.add(q, Par.add(y, z)) == 1n+_ : Nat}
      {==}

# (a + b) + (c + d) regroups as (a + c) + (b + d)
def add_regroup(+a: Nat, +b: Nat, +c: Nat, +d: Nat)
  -> {Par.add(Par.add(a, b), Par.add(c, d)) == Par.add(Par.add(a, c), Par.add(b, d)) : Nat}:
  %add_assoc(a, c, Par.add(b, d)) : {Par.add(Par.add(a, b), Par.add(c, d)) == _ : Nat}
  %add_assoc(a, b, Par.add(c, d)) : {_ == Par.add(a, Par.add(c, Par.add(b, d))) : Nat}
  %add_swap(b, c, d) : {Par.add(a, Par.add(b, Par.add(c, d))) == Par.add(a, _) : Nat}
  {==}

# The loop
# --------

# a loop over m + n numbers is a loop over the first m, then a loop
# over the next n from where the first stopped
def seq_add(m: Nat, n: Nat, +i: Nat)
  -> {Par.add(Par.seq(m, i), Par.seq(n, Par.add(m, i))) == Par.seq(Par.add(m, n), i) : Nat}:
  match m:
    case 0n:
      {==}
    case 1n++q:
      %seq_add(q, n, 1n+i) : {Par.add(Par.add(i, Par.seq(q, 1n+i)), Par.seq(n, 1n+Par.add(q, i))) == Par.add(i, _) : Nat}
      %add_succ(q, i) : {Par.add(Par.add(i, Par.seq(q, 1n+i)), Par.seq(n, 1n+Par.add(q, i))) == Par.add(i, Par.add(Par.seq(q, 1n+i), Par.seq(n, _))) : Nat}
      %add_assoc(i, Par.seq(q, 1n+i), Par.seq(n, 1n+Par.add(q, i))) : {_ == Par.add(i, Par.add(Par.seq(q, 1n+i), Par.seq(n, 1n+Par.add(q, i)))) : Nat}
      {==}

# The tree
# --------

# a leaf is the loop over one number; a node is the loop over 2^p + 2^p
# numbers, split by seq_add into the two halves, each the induction
# hypothesis
def Laws.tree_is_seq(d, i):
  match d:
    case 0n:
      add_zero(i)
    case 1n++p:
      %seq_add(Par.pow2(p), Par.pow2(p), i) : {Par.add(Par.sum_nat(p, i), Par.sum_nat(p, Par.jump(p, i))) == _ : Nat}
      %Laws.tree_is_seq(p, i) : {Par.add(Par.sum_nat(p, i), Par.sum_nat(p, Par.jump(p, i))) == Par.add(_, Par.seq(Par.pow2(p), Par.add(Par.pow2(p), i))) : Nat}
      %Laws.tree_is_seq(p, Par.jump(p, i)) : {Par.add(Par.sum_nat(p, i), Par.sum_nat(p, Par.jump(p, i))) == Par.add(Par.sum_nat(p, i), _) : Nat}
      {==}

# a leaf started one later is one more; a node started one later is
# each half started one later (the induction hypothesis twice, the
# right half's start moved by add_succ), and the four sums regroup
def Laws.tree_leaves(d, i):
  match d:
    case 0n:
      %add_succ(i, 0n) : {_ == 1n+i : Nat}
      %add_zero(i) : {1n+_ == 1n+i : Nat}
      {==}
    case 1n++p:
      %Laws.tree_leaves(p, i) : {Par.add(Par.add(Par.sum_nat(p, i), Par.sum_nat(p, Par.jump(p, i))), Par.add(Par.pow2(p), Par.pow2(p))) == Par.add(_, Par.sum_nat(p, Par.add(Par.pow2(p), 1n+i))) : Nat}
      %add_succ(Par.pow2(p), i) : {Par.add(Par.add(Par.sum_nat(p, i), Par.sum_nat(p, Par.jump(p, i))), Par.add(Par.pow2(p), Par.pow2(p))) == Par.add(Par.add(Par.sum_nat(p, i), Par.pow2(p)), Par.sum_nat(p, _)) : Nat}
      %Laws.tree_leaves(p, Par.jump(p, i)) : {Par.add(Par.add(Par.sum_nat(p, i), Par.sum_nat(p, Par.jump(p, i))), Par.add(Par.pow2(p), Par.pow2(p))) == Par.add(Par.add(Par.sum_nat(p, i), Par.pow2(p)), _) : Nat}
      add_regroup(Par.sum_nat(p, i), Par.sum_nat(p, Par.jump(p, i)), Par.pow2(p), Par.pow2(p))

def Laws.sum_span():
  {==}
