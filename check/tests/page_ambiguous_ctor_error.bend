# a ctor tag with two owners: bend4 ctors are bare and globally
# unique, so the second owner is refused AT DECLARATION (bend3 nulled
# the bare tag at use instead; the one-owner law carries)
type A:
  K{a: U32}

type B:
  K{a: U32, b: U32}

assert f:
  forall v: A
  U32

def f(v):
  match v:
    case K{a}:
      a

assert main:
  U32

def main(): f(K{1})

$$ bend %
Error:
- expected : a fresh constructor name (duplicate declaration: K)
- observed : '{'
Location:
7 | type B:
8>|   K{a: U32, b: U32}
9 |
