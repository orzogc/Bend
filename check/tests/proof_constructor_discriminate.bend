# constructor discrimination from scratch: a Type-computing predicate and
# the explicit-motive transport turn {T2{} == F2{}} into Emp.
# ported from bend3: bend4's rewrite folds right into left, so the raw
# hypothesis transports directly (no sym hop); sym stays as a lemma; the
# != sugar bend4 dropped is spelled as the refuting arrow
type Uni:
  U{}
type Emp:

type Bit:
  T2{}
  F2{}

assert TF:
  forall b: Bit
  Type

def TF(b):
  match b:
    case T2{}:
      Uni
    case F2{}:
      Emp

assert sym:
  forall -A: Type
  forall -a: A
  forall -b: A
  forall e: {a == b : A}
  {b == a : A}

def sym(A, a, b, e):
  %e : {_ == a : A}
  {==}

assert t_ne_f:
  forall e: {T2{} == F2{} : Bit}
  Emp

def t_ne_f(e):
  %e : TF(_)
  U{}

assert ne:
  {T2{} == F2{} : Bit} -> Emp

def ne(): e => t_ne_f(e)

$$ bend %
