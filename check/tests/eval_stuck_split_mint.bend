# a stuck computed match in an eval dump: the printer refolds the
# deref'd form back to the Ref that owns it, so a stuck probe(n) shows
# as probe(n), not as the unfolded match literal (b8e84e6, carried
# into this tree by the a34802d merge: computed and framed matches
# recover their pre-deref form).
# ported from bend3: the arm values become Bool for a readable golden,
# main wraps the stuck call under a lambda (an unapplied def stays
# closed)
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

assert probe:
  forall n: Nat
  Bool

def probe(n):
  match dbl(n):
    case 0n:
      True{}
    case 1n+p:
      False{}

assert main:
  @n:Nat -> Bool

def main():
  n => probe(n)
$$ bend %
n => probe(n)
