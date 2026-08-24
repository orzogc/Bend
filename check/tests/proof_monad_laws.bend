# the three monad laws for a local Maybe: left identity is definitional,
# right identity and associativity close by case analysis and conversion.
# ported from bend3: <A> generics become erased Type parameters; base
# Unit rides Base, the Maybe stays local with its own ctor names
import Base

type Mb<-A: Type>:
  MNone{}
  MSome{x: A}

assert pure:
  @-a: Type -> a -> Mb<a>

def pure(): a => x => MSome{x}

assert bind:
  forall -A: Type
  forall -B: Type
  forall m: Mb<A>
  forall f: A -> Mb<B>
  Mb<B>

def bind(A, B, m, f):
  match m:
    case MNone{}:
      MNone{}
    case MSome{x}:
      f(x)

assert monad_left_id:
  @-a: Type -> @-b: Type -> @-x: a -> @-f: (a -> Mb<b>) -> {bind(a, b, pure(a, x), f) == f(x) : Mb<b>}

def monad_left_id(): a => b => x => f => {==}

assert monad_right_id:
  forall -A: Type
  forall m: Mb<A>
  {bind(A, A, m, pure(A)) == m : Mb<A>}

def monad_right_id(A, m):
  match m:
    case MNone{}:
      {==}
    case MSome{x}:
      {==}

assert monad_assoc:
  forall -T: Type
  forall -u: Type
  forall -V: Type
  forall m: Mb<T>
  forall -f: (T -> Mb<u>)
  forall -g: (u -> Mb<V>)
  {bind(u, V, bind(T, u, m, f), g) == bind(T, V, m, y => bind(u, V, f(y), g)) : Mb<V>}

def monad_assoc(T, u, V, m, f, g):
  match m:
    case MNone{}:
      {==}
    case MSome{x}:
      {==}

assert main:
  Mb<Unit>

def main(): MSome{Unit{}}

$$ bend %
MSome{Unit{}}
