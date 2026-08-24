# Result/Maybe plumbing: a do-block over Result, bind stops at Fail,
# or/map serve defaults
# ported from bend3: Result.or/map and Maybe.some/none/or become local
# ror/rmap and Maybe ctors with Maybe.default; do-binds carry the bend4
# type annotation
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

assert bu:
  forall b: Bool
  U32

def bu(b):
  match b:
    case False{}:
      0
    case True{}:
      1

assert ror:
  forall d: U32
  forall r: Result<U32, U32>
  U32

def ror(d, r):
  match r:
    case Fail{e}:
      d
    case Done{v}:
      v

assert rmap:
  forall f: U32 -> U32
  forall r: Result<U32, U32>
  Result<U32, U32>

def rmap(f, r):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{v}:
      Done{f(v)}

assert resdo:
  Result<U32, U32>

def resdo():
  do Result<U32, U32>:
    x : U32 <- Result.pure(U32, U32, 3)
    y : U32 <- Result.pure(U32, U32, 4)
    return U32.add(U32.mul(x, 10), y)

assert failing:
  Result<U32, U32>

def failing():
  Fail{7}

assert resfail:
  Result<U32, U32>

def resfail():
  do Result<U32, U32>:
    x : U32 <- failing()
    y : U32 <- Result.pure(U32, U32, 4)
    return U32.add(U32.mul(x, 10), y)

assert main.out:
  U32

def main.out():
  b0 = bu(U32.is_eq(ror(99, resdo()), 34))
  b1 = bu(U32.is_eq(ror(99, resfail()), 99))
  b2 = bu(U32.is_eq(ror(9, rmap(x => U32.add(x, 1), resdo())), 35))
  b3 = bu(U32.is_eq(Maybe.default(U32, {Some{5} : Maybe<U32>}, 8), 5))
  b4 = bu(U32.is_eq(Maybe.default(U32, {None{} : Maybe<U32>}, 8), 8))
  U32.add(U32.add(U32.add(U32.add(b0, b1), b2), b3), b4)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
5
$$ bend % --seq
5
exit 0
$$ bend % --par
5
exit 0
$$ bend % --js
5
exit 0
