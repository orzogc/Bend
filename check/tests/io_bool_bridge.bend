# branching survives compilation: recursion through a parity Bool
# dispatch, comparison-fed matches, and a Bool argument all emit plain
# C branches -- the interpreter and every backend agree on 518.
# ported from bend3: the word-case loop becomes Nat fuel with a +U32
# (Cop) mirror (bend4 has no word patterns), if/else becomes
# a Bool match, and bend3's Bool<->word bridge (case 0:/case t: on a
# Bool) is bend3-only -- flip matches real ctors
import Base

assert odd:
  forall x: U32
  Bool

def odd(x):
  U32.is_eq(U32.mod(x, 2), 1)

assert steps:
  forall k: Nat
  forall +n: +U32
  forall acc: U32
  U32

def steps(k, n, acc):
  match k:
    case 0n:
      acc
    case 1n+k2:
      match odd(n):
        case True{}:
          steps(k2, U32.sub(n, 1), U32.add(U32.mul(acc, 2), 1))
        case False{}:
          steps(k2, U32.sub(n, 1), U32.add(acc, 3))

assert flip:
  forall b: Bool
  U32

def flip(b):
  match b:
    case False{}:
      100
    case True{}:
      201

assert main.out:
  U32

def main.out():
  U32.add(U32.add(steps(10n, 10, 0), flip(odd(7))), flip(odd(8)))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
518
$$ bend % --seq
518
exit 0
$$ bend % --par
518
exit 0
$$ bend % --js
518
exit 0
