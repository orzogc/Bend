# Nat literals are BIDIRECTIONAL: 2n parses to Succ{Succ{Zero{}}}, and
# the printer renders closed chains back as Nn -- inside tuples and
# ctor spines alike. A broken chain (Succ of a var) prints plain.
# ported from bend3: list literals become Con/Nil spines, the stuck
# def rides the tuple as a lambda component; no C lane (a List is not
# C-showable)
import Base

assert dbl:
  forall n: Nat
  Nat

def dbl(n):
  match n:
    case 0n:
      0n
    case 1n+p:
      Succ{Succ{dbl(p)}}

assert main:
  Pair(Nat, Pair(Nat, Pair(List<Nat>, @k:Nat -> Nat)))

def main():
  (dbl(2n), 0n, Con{3n, Con{dbl(1n), Nil{}}}, n => Succ{n})
$$ bend %
Tuple{4n, Tuple{0n, Tuple{Con{3n, Con{2n, Nil{}}}, n => 1n+n}}}
$$ bend % --js
Error: main must answer IO<T>
exit 1
