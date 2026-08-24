# bend3's harness-cache adversary, purity side: interleaved --eval
# blocks of DIFFERENT defs repeated byte-identically off one cached
# book. bend4's runner caches the checked book per file; interleaved
# --show pages of two defs and the value block must repeat unchanged
import Base

assert grow:
  forall n: Nat
  Nat

def grow(n):
  match n:
    case Zero{}:
      1n
    case Succ{k}:
      Succ{Succ{grow(k)}}

assert shrink:
  forall n: Nat
  Nat

def shrink(n):
  match n:
    case Zero{}:
      0n
    case Succ{k}:
      k

assert main:
  Nat

def main():
  shrink(grow(5n))
$$ bend % --show grow
grow = \{Zero: 1n; Succ: (k => 2n+grow(k))}
$$ bend % --show shrink
shrink = \{Zero: 0n; Succ: (k => k)}
$$ bend % --show grow
grow = \{Zero: 1n; Succ: (k => 2n+grow(k))}
$$ bend %
10n
$$ bend %
10n
