# SPEC PART 3 COP in a book that never imports Base: the locally
# declared trio must be the locked one (Copiable spelled on Sigma,
# no Pair in scope), and a match on a Many Cop scrutinee hands its
# fields out at Many, so an arm may consume a field twice
type Sigma<-A: Type, -B: @-x: A -> Type>:
  Tuple{fst: A, snd: B(fst)}

assert Copy:
  forall -A: Type
  forall -x: A
  Type

def Copy(A, x):
  &y: A -> {x == y : A}

assert Copiable:
  forall -T: Type
  Type

def Copiable(T):
  @x: T -> Sigma<Copy(T, x), _ => Copy(T, x)>

type Nat:
  Zero{}
  Succ{pred: Nat}

assert Nat.add:
  forall a: Nat
  forall b: Nat
  Nat

def Nat.add(a, b):
  match a:
    case Zero{}:
      b
    case Succ{p}:
      Succ{Nat.add(p, b)}

assert Equal.cong:
  forall -A: Type
  forall -B: Type
  forall -f: @-x: A -> B
  forall -a: A
  forall -b: A
  forall e: {a == b : A}
  {f(a) == f(b) : B}

def Equal.cong(A, B, f, a, b, e):
  %e@e : {f(a) == f(_) : B}
  {==}

assert Nat.copy:
  forall n: Nat
  Sigma<Copy(Nat, n), _ => Copy(Nat, n)>

def Nat.copy(n):
  match n:
    case Zero{}:
      Tuple{Tuple{Zero{}, {==}}, Tuple{Zero{}, {==}}}
    case Succ{p}:
      Tuple{Tuple{a, ea}, Tuple{b, eb}} = Nat.copy(p)
      pa = Equal.cong(Nat, Nat, x => Succ{x}, p, a, ea)
      pb = Equal.cong(Nat, Nat, x => Succ{x}, p, b, eb)
      Tuple{Tuple{Succ{a}, pa}, Tuple{Succ{b}, pb}}

assert addself:
  forall +x: +Nat
  Nat

def addself(x):
  match x:
    case Zero{}:
      Zero{}
    case Succ{p}:
      Succ{Nat.add(p, p)}

assert main:
  Nat

def main():
  addself(Succ{Succ{Zero{}}})
$$ bend %
3n
