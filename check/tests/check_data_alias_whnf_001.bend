# red-team pin carried from bend3: a ctor field whose type is a FULL
# application of a Def type alias must check -- the checker whnfs the
# field type, so alias(U32) reduces to U32 and a MkW2 builds and
# matches. No sharing here: the port is strict.
# ported from bend3: match heads a def body only, so the match moved
# into get; ctor names are bare and globally unique (W.K -> MkW2)
import Base

assert alias:
  forall T: Type
  Type

def alias(T):
  T

type W2:
  MkW2{v: alias(U32)}

assert get:
  forall w: W2
  U32

def get(w):
  match w:
    case MkW2{v}:
      v

assert main.out:
  U32

def main.out():
  get({MkW2{42} : W2})

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
