# erased argument (-T): polymorphic first-order def
# ported from bend3 (Data -> Type)
import Base

type BoxA<-T: Type>:
  MkBoxA{v: T}

assert get:
  forall -T: Type
  forall b: BoxA<T>
  T

def get(T, b):
  match b:
    case MkBoxA{v}:
      v

assert main.out:
  U32

def main.out():
  get(U32, MkBoxA{7})

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
7
$$ bend % --seq
7
exit 0
$$ bend % --par
7
exit 0
$$ bend % --js
7
exit 0
