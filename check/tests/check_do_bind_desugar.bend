# bend3's splice law made do-binds agree with their desugaring at
# generic pair yields; bend4's do reads the bind types as spelled, and
# the nested-pair yields ride Result whole (the ++ half was Cat over
# a pair-element List: bend4's ++ is String.append, pending wider
# ruling, so that half stays out)
import Base

assert f8:
  Result<U32, F32 & Unit>

def f8():
  Done{(1.5, Unit{})}

assert g8:
  Result<U32, U32 & (F32 & Unit)>

def g8():
  Done{(7, (2.5, Unit{}))}

assert prog:
  Result<U32, U32>

def prog():
  do Result<U32, U32>:
    x : F32 & Unit <- f8()
    y : U32 & (F32 & Unit) <- g8()
    return 0

assert unwrap:
  forall r: Result<U32, U32>
  U32

def unwrap(r):
  match r:
    case Done{v}:
      v
    case Fail{x}:
      x

assert main.out:
  Nat

def main.out():
  U32.to_nat(unwrap(prog()))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
0n
$$ bend % --seq
0n
exit 0
$$ bend % --par
0n
exit 0
$$ bend % --js
0n
exit 0
