# bend3's family wall, both halves carried: an either of Data
# components contracted freely while a closure-holding either refused
# multi-use. bend4 is affine for every type, so the free half becomes
# twice's explicit +e Cop binder over Either.copy -- and the wall
# half lands
# on the SAME def: leak's bare e spends twice and refuses at leak,
# closure or not.
# ported from bend3: U32 | U32 -> Either<U32, U32> (base Inl/Inr; no |
# type sugar); leak's let-then-match routes through leak.go
import Base

assert Either.copy:
  forall -c1: Copiable(U32)
  forall -c2: Copiable(U32)
  forall t: Either<U32, U32>
  Copy(Either<U32, U32>, t) & Copy(Either<U32, U32>, t)

def Either.copy(c1, c2, t):
  match t:
    case Inl{v}:
      ((vx, ve), (vy, vf)) = U32.copy(v)
      p1 = Equal.cong(U32, Either<U32, U32>, z => Inl{z}, v, vx, ve)
      p2 = Equal.cong(U32, Either<U32, U32>, z => Inl{z}, v, vy, vf)
      ((Inl{vx}, p1), (Inl{vy}, p2))
    case Inr{v}:
      ((vx, ve), (vy, vf)) = U32.copy(v)
      p1 = Equal.cong(U32, Either<U32, U32>, z => Inr{z}, v, vx, ve)
      p2 = Equal.cong(U32, Either<U32, U32>, z => Inr{z}, v, vy, vf)
      ((Inr{vx}, p1), (Inr{vy}, p2))

assert side:
  forall e: Either<U32, U32>
  U32

def side(e):
  match e:
    case Inl{value}:
      value
    case Inr{value}:
      value + 1

assert twice:
  forall +e: (+ Either<U32, U32> ~ Either.copy(U32.copy, U32.copy))
  U32

def twice(e):
  side(e) + side(e)

assert la:
  forall e: Either<U32, U32 -> U32>
  U32

def la(e):
  match e:
    case Inl{value}:
      value
    case Inr{f}:
      f(0)

assert leak.go:
  forall e: Either<U32, U32 -> U32>
  forall x: U32
  U32

def leak.go(e, x):
  match e:
    case Inl{value}:
      value
    case Inr{f}:
      f(x)

assert leak:
  forall e: Either<U32, U32 -> U32>
  U32

def leak(e):
  leak.go(e, la(e))

assert main:
  U32

def main(): twice(Inr{2})
$$ bend %
Error:
- expected : e
- observed : e (consumed more than once)
Location: leak
