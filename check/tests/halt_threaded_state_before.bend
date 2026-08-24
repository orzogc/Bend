# bend3's found-column search accepted a growing accumulator BEFORE
# the decreasing column; bend4's left-to-right law refuses a non-EQ
# column ahead of the descent (halt_threaded_state_after pins the
# accepted order)
import Base

assert go:
  forall acc: U32
  forall n: Nat
  U32

def go(acc, n):
  match n:
    case Zero{}:
      acc
    case Succ{p}:
      go(acc + 1, p)

assert main:
  Nat

def main():
  U32.to_nat(go(10, 3n))
$$ bend %
Error:
- expected : a decreasing self-call (some live argument must shrink)
- observed : go(U32.add(acc, U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}), p)
Context:
- acc : U32
- p   : Nat
Location: go
16 |     case Succ{p}:
17>|       go(acc + 1, p)
18 |
