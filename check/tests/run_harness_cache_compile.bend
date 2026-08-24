# bend3's harness-cache adversary, compile side: compile and eval
# blocks shared one cached checked book and stayed pure. bend4's
# runner shares one in-process book across a file's blocks the same
# way (no --compile flag; --show is the compile-side page): the value
# and the rendered page must repeat byte-identically
import Base

assert double:
  forall n: Nat
  Nat

def double(n):
  match n:
    case Zero{}:
      0n
    case Succ{k}:
      Succ{Succ{double(k)}}

assert main:
  Nat

def main():
  double(3n)
$$ bend % --show double
double = \{Zero: 0n; Succ: (k => 2n+double(k))}
$$ bend %
6n
$$ bend % --show double
double = \{Zero: 0n; Succ: (k => 2n+double(k))}
$$ bend %
6n
