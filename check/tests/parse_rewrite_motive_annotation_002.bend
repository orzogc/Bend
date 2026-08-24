# bend3 refused the '_' motive at the Type carrier; bend4 binds it, so
# symmetry at ANY carrier -- Type itself included -- and the transport
# cast both CHECK: the inverted law at Type:Type
import Base

assert symT:
  forall -t: Type
  forall -x: t
  forall -y: t
  forall e: {x == y : t}
  {y == x : t}

def symT(t, x, y, e):
  %e : {_ == x : t}
  {==}

assert cast:
  forall -A: Type
  forall -B: Type
  forall e: {A == B : Type}
  forall x: A
  B

def cast(A, B, e, x):
  %e : _
  x

assert main.out:
  U32

def main.out():
  0

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
0
$$ bend % --seq
0
exit 0
$$ bend % --par
0
exit 0
$$ bend % --js
0
exit 0
