# A | B is core grammar (Either), gated on nothing but the name --
# with Base it is Either<A, B> (bend3 gated the bare | on `import
# Either`)
import Base

assert pick:
  forall e: U32 | Bool
  U32

def pick(e):
  match e:
    case Inl{u}:
      u
    case Inr{b}:
      if b: 1 else: 0

assert main.out:
  U32

def main.out():
  pick({Inl{7} : U32 | Bool}) * 10 + pick({Inr{True{}} : U32 | Bool})

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
71
$$ bend % --seq
71
exit 0
$$ bend % --js
71
exit 0
