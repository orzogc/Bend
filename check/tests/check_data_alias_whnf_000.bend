# bend3 checked Data structurally on demand and saw through aliases
# (wnf), so a Type-valued def classified where Data was demanded. bend4
# keeps the alias transparency -- a bare def ref types a binder -- and
# the over-use rides + d ~ U32.copy, whose witness types only BECAUSE
# the alias unfolds to U32 (core is affine for every type; there is no
# on-demand Data class), strict.
# ported from bend3: x + x spends x twice, so x binds +
import Base

assert d:
  Type

def d(): U32

assert two:
  forall +x: (+ d ~ U32.copy)
  U32

def two(x):
  x + x

assert main.out:
  U32

def main.out(): two(5)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
10
$$ bend % --seq
10
exit 0
$$ bend % --par
10
exit 0
$$ bend % --js
10
exit 0
