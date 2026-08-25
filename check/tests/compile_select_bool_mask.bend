# the branchless Bool select coverage, GOAL 1.4: a two-arm Bool match
# whose arms are constant equality tests on one variable -- reached
# through the b2u bridge and Bool.or -- folds to one equality test
# over an OR-mask (nested U32_BIN). This is gameoflife's rule algebra on a fresh domain (a
# quorum vote: 5 votes pass, or 4 with the chair's credit), so the
# peephole is pinned outside bench/.
# csrc has: U32_BIN(U32_BIN(
import Base

assert b2u:
  forall b: Bool
  U32

def b2u(b):
  match b:
    case False{}: 0
    case True{}: 1

assert quorum_strict:
  forall v: U32
  U32

def quorum_strict(v):
  b2u(U32.is_eq(v, 5))

assert quorum_loose:
  forall +v: +U32
  U32

def quorum_loose(v):
  b2u(Bool.or(U32.is_eq(v, 4), U32.is_eq(v, 5)))

assert decide:
  forall chair: U32
  forall v: U32
  U32

def decide(chair, v):
  match U32.is_zero(chair):
    case True{}:
      quorum_strict(v)
    case False{}:
      quorum_loose(v)

assert tally:
  forall +i: +Nat
  U32

def tally(i):
  match i:
    case 0n:
      0
    case 1n+p:
      U32.add(decide(U32.mod(U32.from_nat(p), 2), U32.mod(U32.from_nat(p), 7)), tally(p))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(tally(64n)))
$$ bend %
13
$$ bend % --seq
13
exit 0
$$ bend % --par
13
exit 0
$$ bend % --js
13
exit 0
