# audit carried: bend3's Pair table was [0, 1] -- Data iff both
# arguments are -- so Pair(U32, U32) shared. bend4 has no table and no
# param bounds: the two-param datatype forms over Type and a single
# spend builds and matches strict, no #[halts] needed.
# ported from bend3: type Pair(A: Data, B: Data) -> type Pr7<A: Type,
# B: Type>; the let-then-match main routes through get
import Base

type Pr7<A: Type, B: Type>:
  MkPr7{x: A, y: B}

assert get:
  forall p: Pr7<U32, U32>
  U32

def get(p):
  match p:
    case MkPr7{x, y}:
      x + y

assert main.out:
  U32

def main.out():
  get({MkPr7{20, 22} : Pr7<U32, U32>})

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
42
$$ bend % --seq
42
exit 0
$$ bend % --par
42
exit 0
$$ bend % --js
42
exit 0
