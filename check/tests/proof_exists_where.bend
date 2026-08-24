# witness, evidence and claim pack as nested sigmas; the fill returns the
# right-nested triple.
# ported from bend3: bend3's `exists y where P` interleaved the evidence,
# while bend4's where packs the clause into a pair the claim cannot see
# through -- the evidence is its own exists clause instead; Nat replaces
# U32 to keep the printed witness a literal
import Base

assert pick:
  exists y: Nat
  exists e: {y == 2n : Nat}
  {Nat.add(y, 1n) == 3n : Nat}

def pick():
  (2n, {==}, {==})

assert main:
  Sigma<Nat, y => Sigma<{y == 2n : Nat}, e => {Nat.add(y, 1n) == 3n : Nat}>>

def main(): pick()

$$ bend %
Tuple{2n, Tuple{{==}, {==}}}
