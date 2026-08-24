# base Maybe: pure/map compute through, None serves the default.
# ported from bend3: Maybe.some/none become Some/None, Maybe.or becomes
# Maybe.default (bend4's arg order: A, m, d), map becomes a local def
# (bend4 base has none); result 507 (bend3's golden) shown as a Nat
import Base

assert Maybe.default:
  forall -A: Type
  forall m: Maybe<A>
  forall d: A
  A

def Maybe.default(A, m, d):
  match m:
    case None{}:
      d
    case Some{x}:
      x

assert mmap:
  forall f: @x:U32 -> U32
  forall m: Maybe<U32>
  Maybe<U32>

def mmap(f, m):
  match m:
    case None{}:
      None{}
    case Some{value}:
      Some{f(value)}

assert main.out:
  Nat

def main.out():
  U32.to_nat(U32.add(U32.mul(Maybe.default(U32, mmap(x => U32.add(x, 1), Maybe.pure(U32, 4)), 9), 100), Maybe.default(U32, None{}, 7)))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
507n
$$ bend % --seq
507n
exit 0
$$ bend % --par
507n
exit 0
$$ bend % --js
507n
exit 0
