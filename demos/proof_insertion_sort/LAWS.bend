# proof_insertion_sort: the laws. The human states them; PROOF.bend
# must prove them. Lean's Mathlib states the same pair for insertion
# sort: List.sorted_insertionSort and List.perm_insertionSort. A
# permutation is stated by counts: every value occurs in the output as
# often as in the input. The third law, that sort keeps the length,
# follows from the second but has its own short proof.

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
