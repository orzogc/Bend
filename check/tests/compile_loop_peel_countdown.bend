# bend3's literal-countdown peel (comp_loops C.unrl) pinned csrc
# shapes bend4's tocl does not have (no peel pass, and the key
# dispatch's literal patterns are word views tocl refuses anyway);
# the loop's VALUE carries on a Nat countdown, interp and js
import Base

assert key:
  forall j: U32
  U32

def key(j):
  match j:
    case 0:
      13
    case 1:
      57
    case j:
      31

assert mix:
  forall n: Nat
  forall j: U32
  forall x: U32
  U32

def mix(n, j, x):
  match n:
    case Zero{}:
      x
    case Succ{k}:
      ((j1, d1), (j2, d2)) = U32.copy(j)
      mix(k, j1 + 1, ((x * 5) + key(j2)) .&. 65535)

assert main.out:
  Nat

def main.out():
  U32.to_nat(mix(6n, 0, 1) + mix(6n, 0, 2))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
77975n
$$ bend % --js
77975n
exit 0
