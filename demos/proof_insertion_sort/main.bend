# proof_insertion_sort: insertion sort on lists of Base's Nat, with the
# vocabulary its laws need: Sorted (a computed type), count (how many
# times a value occurs) and length. main prints sort([3n, 1n, 2n]).
# LAWS.bend states that sort's output is sorted, has the same counts
# and the same length as its input; PROOF.bend proves it.
#
#   bend demos/proof_insertion_sort/main.bend
#
# The comparison returns evidence: le_case(x, h) is OL{e} with e a
# proof of x <= h, or OG{e} with e a proof of h <= x. insert branches
# on that verdict through dec, so a proof about insert can branch on
# the same fact the program did.

import Base

# Order
# -----

# LE(a, b) is the type of proofs of a <= b: Unit when it holds, Empty
# when it fails
def LE(a: Nat, b: Nat) -> Data:
  match a:
    case 0n:
      Unit
    case 1n+a1:
      match b:
        case 0n:
          Empty
        case 1n+b1:
          LE(a1, b1)

# the verdict of a comparison, with its evidence
type LEOr<-x: Nat, -h: Nat> is Data:
  OL{e: LE(x, h)}
  OG{e: LE(h, x)}

def le_case.fin(-a: Nat, -b: Nat, w: LEOr<a, b>) -> LEOr<1n+a, 1n+b>:
  match w:
    case OL{e}:
      OL{e}
    case OG{e}:
      OG{e}

def le_case(x: Nat, h: Nat) -> LEOr<x, h>:
  match x h:
    case 0n 0n:
      OL{Unit{}}
    case 0n 1n+b:
      OL{Unit{}}
    case 1n+a 0n:
      OG{Unit{}}
    case 1n+a 1n+b:
      le_case.fin(a, b, le_case(a, b))

# Sorting
# -------

# where x goes, given the verdict c against the head h; r is x
# inserted into the tail t
def dec(x: Nat, h: Nat, t: List<&2, Nat>, r: List<&2, Nat>, c: LEOr<x, h>) -> List<&2, Nat>:
  match c:
    case OL{e}:
      x <> h <> t
    case OG{e}:
      h <> r

def insert(+x: Nat, +xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      [x]
    case h <> t:
      dec(x, h, t, insert(x, t), le_case(x, h))

def sort(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      insert(h, sort(t))

# The vocabulary of the laws
# --------------------------

# Sorted.from(lo, xs): every element is at least lo, and the list
# ascends; the bound moves to each head as the list is walked
def Sorted.from(lo: Nat, xs: List<&2, Nat>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case h <> t:
      (LE(lo, h) & Sorted.from(h, t))

def Sorted(xs: List<&2, Nat>) -> Type:
  Sorted.from(0n, xs)

def eq(a: Nat, b: Nat) -> Bool:
  Cmp.is_eq(Nat.cmp(a, b))

# n plus one when b holds
def bump(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}:
      1n+n
    case False{}:
      n

# how many times x occurs in xs
def count(+x: Nat, xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      bump(eq(x, h), count(x, t))

def length(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      1n+length(t)

# Main
# ----

def main() -> List<&2, Nat>:
  sort([3n, 1n, 2n])
