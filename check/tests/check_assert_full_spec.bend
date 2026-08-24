# the full assert spec shape: `forall x : T where P` (the clause packs
# into a sigma &x:T -> P), `exists y : T` (the result sigma), a closing
# equation -- and its fill, an unannotated def whose param binds the
# packed clause. The proof runs: an impossible arm dies by \{} on the
# where-evidence, the inductive arm rewrites the IH.
# ported from bend3: the where witness is the SIGMA, so the equation
# projects it (Sigma.fst) and the fill destructures before a helper
# (nested matches go in binder order)
import Base

assert Sigma.fst:
  forall -A: Type
  forall -B: @-x: A -> Type
  forall p: Sigma<A, B>
  A

def Sigma.fst(A, B, p):
  match p:
    case (x, y):
      x

assert IsEven:
  forall x: Nat
  Type

def IsEven(x):
  match x:
    case Zero{}:
      Unit
    case Succ{p}:
      match p:
        case Zero{}:
          Empty
        case Succ{q}:
          IsEven(q)

assert go:
  forall n: Nat
  forall e: IsEven(n)
  (&y:Nat -> {Nat.mul(y, 2n) == n : Nat})

def go(n, e):
  match n:
    case Zero{}:
      (0n, {==})
    case Succ{p}:
      match p:
        case Zero{}:
          \{}(e)
        case Succ{q}:
          (y, prf) = go(q, e)
          (Succ{y}, %h@prf : {Nat.mul(Succ{y}, 2n) == Succ{Succ{_}} : Nat}; {==})

assert my_thesis:
  forall x : Nat where IsEven(x)
  exists y : Nat
  {Nat.mul(y, 2n) == Sigma.fst(Nat, k => IsEven(k), x) : Nat}

def my_thesis(x):
  (n, e) = x
  go(n, e)

assert main:
  &y:Nat -> {Nat.mul(y, 2n) == 6n : Nat}

def main(): my_thesis((6n, Unit{}))
$$ bend %
Tuple{3n, {==}}
