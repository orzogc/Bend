# Base Nat ordering as a type FAMILY: LE computes to Unit on concrete
# pairs, le_trans chains them, and the family (refl/zero/succ/antisym)
# instantiates
# ported from bend3: evidence params are trailing (a, b, c, ab, bc), not
# interleaved; Unit's value is Unit{}; the checker-silent bend3 golden
# becomes the interp lane printing main's Unit witness
import Base

assert Nat.LE:
  forall a: Nat
  forall b: Nat
  Type

def Nat.LE(a, b):
  match a b:
    case 0n y:
      Unit
    case 1n+x 0n:
      Empty
    case 1n+x 1n+y:
      Nat.LE(x, y)

assert Nat.le_refl:
  forall a: Nat
  Nat.LE(a, a)

def Nat.le_refl(a):
  match a:
    case 0n:
      Unit{}
    case 1n+x:
      Nat.le_refl(x)

assert Nat.le_zero:
  forall -b: Nat
  Nat.LE(0n, b)

def Nat.le_zero(b):
  Unit{}

assert Nat.le_succ:
  forall a: Nat
  forall b: Nat
  forall e: Nat.LE(a, b)
  Nat.LE(a, 1n+b)

def Nat.le_succ(a, b, e):
  match a:
    case 0n:
      Unit{}
    case 1n+x:
      match b:
        case 0n:
          Empty.absurd(Nat.LE(x, 0n), e)
        case 1n+y:
          Nat.le_succ(x, y, e)

assert Nat.le_trans:
  forall a: Nat
  forall b: Nat
  forall c: Nat
  forall ab: Nat.LE(a, b)
  forall bc: Nat.LE(b, c)
  Nat.LE(a, c)

def Nat.le_trans(a, b, c, ab, bc):
  match a:
    case 0n:
      Unit{}
    case 1n+x:
      match b:
        case 0n:
          Empty.absurd(Nat.LE(1n+x, c), ab)
        case 1n+y:
          match c:
            case 0n:
              Empty.absurd(Nat.LE(1n+x, 0n), bc)
            case 1n+z:
              Nat.le_trans(x, y, z, ab, bc)

assert Nat.le_antisym:
  forall a: Nat
  forall b: Nat
  forall ab: Nat.LE(a, b)
  forall ba: Nat.LE(b, a)
  {a == b : Nat}

def Nat.le_antisym(a, b, ab, ba):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      Empty.absurd({0n == 1n+y : Nat}, ba)
    case 1n+x 0n:
      Empty.absurd({1n+x == 0n : Nat}, ab)
    case 1n+x 1n+y:
      Equal.cong(Nat, Nat, k => 1n+k, x, y, Nat.le_antisym(x, y, ab, ba))

assert e13:
  Nat.LE(1n, 3n)

def e13():
  Nat.le_trans(1n, 2n, 3n, Unit{}, Unit{})

assert refl9:
  Nat.LE(9n, 9n)

def refl9():
  Nat.le_refl(9n)

assert zero7:
  Nat.LE(0n, 7n)

def zero7():
  Nat.le_zero(7n)

assert succ25:
  Nat.LE(2n, 5n)

def succ25():
  Nat.le_succ(2n, 4n, Nat.le_succ(2n, 3n, Nat.le_succ(2n, 2n, Nat.le_refl(2n))))

assert anti4:
  {4n == 4n : Nat}

def anti4():
  Nat.le_antisym(4n, 4n, Nat.le_refl(4n), Nat.le_refl(4n))

assert main:
  Nat.LE(1n, 3n)

def main():
  e13()
$$ bend %
Unit{}
