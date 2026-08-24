# nullary and single-word ctors under contraction and discard: a value
# used twice, an unused binder, and a mixed-type boundary all compile
# ported from bend3: shares become +lets, the counter walks a Nat
import Base

type Dir:
  Nn{}
  Ss{}

assert Dir.copy:
  forall t: Dir
  Copy(Dir, t) & Copy(Dir, t)

def Dir.copy(t):
  match t:
    case Nn{}:
      ((Nn{}, {==}), (Nn{}, {==}))
    case Ss{}:
      ((Ss{}, {==}), (Ss{}, {==}))

type Code:
  Cc{v: U32}

assert Code.copy:
  forall t: Code
  Copy(Code, t) & Copy(Code, t)

def Code.copy(t):
  match t:
    case Cc{v}:
      ((vx, ve), (vy, vf)) = U32.copy(v)
      s10 = Equal.cong(U32, Code, z => Cc{z}, v, vx, ve)
      s20 = Equal.cong(U32, Code, z => Cc{z}, v, vy, vf)
      ((Cc{vx}, s10), (Cc{vy}, s20))

type BoxB:
  NilB{}
  TwoB{a: U32, b: U32}

assert dir_val:
  forall d: Dir
  U32

def dir_val(d):
  match d:
    case Nn{}:
      1
    case Ss{}:
      2

assert code_val:
  forall c: Code
  U32

def code_val(c):
  match c:
    case Cc{v}:
      v

assert toss:
  forall d: Dir
  forall x: U32
  U32

def toss(d, x):
  x

assert box_val:
  forall b: BoxB
  U32

def box_val(b):
  match b:
    case NilB{}:
      0
    case TwoB{a, b}:
      U32.add(a, b)

assert spin:
  forall +i: +Nat
  forall acc: U32
  U32

def spin(i, acc):
  match i:
    case 0n:
      acc
    case 1n+p:
      +d = {Nn{} : +Dir}
      +c = {Cc{U32.add(U32.from_nat(p), 41)} : +Code}
      a1 = U32.add(dir_val(d), dir_val(d))
      a2 = U32.add(code_val(c), code_val(c))
      a3 = box_val(TwoB{U32.add(U32.from_nat(p), 1), 3})
      spin(p, toss(Ss{}, U32.mod(U32.add(U32.add(U32.add(acc, a1), a2), a3), 65521)))

assert main.out:
  U32

def main.out():
  spin(10n, 0)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
1015
$$ bend % --seq
1015
exit 0
$$ bend % --par
1015
exit 0
$$ bend % --js
1015
exit 0
