# bend3's 46->95 flattening collision (A_B.X vs A.B_X both reading
# A_B_X in C); bend4 has no qualified ctor names to flatten -- the
# bare names X_c and B_X are simply distinct, every site resolves by
# name, and both builds answer alike
import Base

type A_B6:
  X_c{v: U32}

type A6b:
  B_X{v: U32}

assert f:
  forall x: A_B6
  forall y: A6b
  U32

def f(x, y):
  match x:
    case X_c{v}:
      match y:
        case B_X{w}:
          v + w

assert main.out:
  Nat

def main.out():
  U32.to_nat(f(X_c{30}, B_X{12}))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
42n
$$ bend % --seq
42n
exit 0
$$ bend % --par
42n
exit 0
$$ bend % --js
42n
exit 0
