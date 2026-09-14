# HVM5 in Bend -- the laws. Claims about the pure logic under the
# evaluator: the parser's string cursor, the run words that pack a
# chain of #0/#1 constructors into one word, the name codes and the
# book's depth. PROOF.bend proves them.

import Base
import ./main.bend as Hvm

# LAW: the parser's cursor: the code at position n of s is the code
# at the head of s past n characters.
law at_drop:
  for +s: String
  for +n: Nat
  {Hvm.str_at(Hvm.str_drop(s, n), 0n) == Hvm.str_at(s, n) : U32}

# LAW: a bit pushed outermost onto a run word is the bit bit0 reads
# back, and popping it restores the word (here the one-bit run #1{..},
# for either bit).
law run_push_pop:
  for +b: Bool
  {(Hvm.bit0(Hvm.run_push(Hvm.run_word(1, 1), Hvm.pick(U32, b, 1, 0))),
    Hvm.run_pop(Hvm.run_push(Hvm.run_word(1, 1), Hvm.pick(U32, b, 1, 0))))
   == (Bool.not(b), Hvm.run_word(1, 1)) : Bool & U32}

# LAW: a name survives its code: the parser's six-bits-per-character
# code of a name prints back as the name.
law name_round_trip:
  {(Hvm.nam(Hvm.name_code("main", 0)), Hvm.nam(Hvm.name_code("F", 0)))
   == ("main", "F") : String & String}

# LAW: the book's depth is the least d with 2^d slots for n
# definitions.
law book_depth_fits:
  {(Hvm.book_depth(32n, 1, 0n), Hvm.book_depth(32n, 5, 0n), Hvm.book_depth(32n, 8, 0n),
    Hvm.book_depth(32n, 9, 0n))
   == (0n, 3n, 3n, 4n) : Nat & Nat & Nat & Nat}
