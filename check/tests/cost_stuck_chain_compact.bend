# bend3's stuck-wnf tripwire, re-pinned as bend4's own live class: the
# 16-deep share chain's counter is gone (no --stats), but the compact-
# chain claim itself fails here -- a division's result fed through a
# multiplication, nested twice as a match's computed scrutinee, blows
# the evaluator; the intended golden is the value every sound lane
# answers
import Base

assert prng:
  forall +s: +U32
  U32

def prng(s):
  (s / 3) * 65537

assert mix:
  forall s0: U32
  U32

def mix(s0):
  match prng(prng(s0)):
    case 0:
      1
    case n:
      2

assert main.out:
  Nat

def main.out():
  U32.to_nat(mix(7))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
2n
$$ bend % --js
2n
exit 0
