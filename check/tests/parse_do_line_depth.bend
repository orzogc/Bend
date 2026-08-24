# bend3 rejected a do line shallower than its head (the line-depth
# page); bend4 blocks are layout-free by design, so the same shallow
# line parses, binds, and the value proves it
import Base

assert f:
  Result<U32, U32>

def f():
  do Result<U32, U32>:
  x : U32 <- Done{1}
    return x

assert unwrap:
  forall r: Result<U32, U32>
  U32

def unwrap(r):
  match r:
    case Done{v}:
      v
    case Fail{x}:
      x

assert main.out:
  Nat

def main.out():
  U32.to_nat(unwrap(f()))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
1n
$$ bend % --seq
1n
exit 0
$$ bend % --par
1n
exit 0
$$ bend % --js
1n
exit 0
