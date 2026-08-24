# bend3's nullary-ctor enum had table [] -- always Data -- so a Token
# shared and owned freely. bend4 is affine for enums too: the free
# sharing becomes the explicit +Token Cop binder over the local
# Token.copy witness, and the same three flips answer the same 2.
# ported from bend3: t = (Token.Yes{} : Token) becomes a +let with the
# brace Ann; ctor names are bare
import Base

type Token:
  Yes{}
  No{}

assert Token.copy:
  forall t: Token
  Copy(Token, t) & Copy(Token, t)

def Token.copy(t):
  match t:
    case Yes{}:
      ((Yes{}, {==}), (Yes{}, {==}))
    case No{}:
      ((No{}, {==}), (No{}, {==}))

assert flip:
  forall t: Token
  U32

def flip(t):
  match t:
    case Yes{}:
      1
    case No{}:
      0

assert main.out:
  U32

def main.out():
  +t = {Yes{} : +Token}
  (flip(t) + flip(t)) + flip(No{})

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
2
$$ bend % --seq
2
exit 0
$$ bend % --par
2
exit 0
$$ bend % --js
2
exit 0
