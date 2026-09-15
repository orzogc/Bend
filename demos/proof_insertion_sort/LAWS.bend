# proof_insertion_sort: the laws. The human states them; PROOF.bend
# must prove them. Lean's Mathlib states the same pair for insertion
# sort: List.sorted_insertionSort and List.perm_insertionSort. A
# permutation is stated by counts: every value occurs in the output as
# often as in the input. The third law, that sort keeps the length,
# follows from the second but has its own short proof. The fourth
# says a sorted list is a fixed point of sort, so sort is idempotent
# (the fifth). The sixth says the head of the output is a lower bound
# of the whole input: sort finds the minimum.

import Base
import ./main.bend as Sort

# LAW: the output of sort is sorted: it ascends, starting at 0n
law sort_sorted:
  for +xs: List<&2, Nat>
  Sort.Sorted(Sort.sort(xs))

# LAW: sort permutes its input: every value x occurs in sort(xs) as
# often as it occurs in xs
law sort_perm:
  for +x  : Nat
  for +xs : List<&2, Nat>
  {Sort.count(x, Sort.sort(xs)) == Sort.count(x, xs) : Nat}

# LAW: sort keeps the length of its input
law sort_length:
  for +xs: List<&2, Nat>
  {Sort.length(Sort.sort(xs)) == Sort.length(xs) : Nat}

# LAW: sort keeps a sorted list as it is: a list that ascends from
# any bound lo is a fixed point of sort
law sort_fixed:
  for +xs : List<&2, Nat>
  for -lo : Nat
  for  s  : Sort.Sorted.from(lo, xs)
  {xs == Sort.sort(xs) : List<&2, Nat>}

# LAW: sort is idempotent: sorting twice is sorting once
law sort_idem:
  for +xs: List<&2, Nat>
  {Sort.sort(Sort.sort(xs)) == Sort.sort(xs) : List<&2, Nat>}

# LAW: the head of sort's output is at most every element of its
# input: if sort(xs) is m <> t then m is below all of xs
law sort_min:
  for +m  : Nat
  for  t  : List<&2, Nat>
  for +xs : List<&2, Nat>
  for  e  : {m <> t == Sort.sort(xs) : List<&2, Nat>}
  Sort.Below(m, xs)
