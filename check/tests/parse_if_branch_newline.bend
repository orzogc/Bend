# bend4 blocks are layout-free: branches split across lines however
# they like (bend3 pinned a newline law; no counterpart wall exists)
import Base

assert f:
  forall b: Bool
  U32

def f(b):
  if b:
      100
  else:
        7

assert main.out:
  U32

def main.out():
  f(False{})

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
7
$$ bend % --seq
7
exit 0
$$ bend % --js
7
exit 0
