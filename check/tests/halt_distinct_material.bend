# bend3's distinctness pin (wnf(bod(fun)) spends fun twice) meets a
# wall one rule earlier in bend4: the self-call's argument bod(fun)
# is not a shrinking column, so infer-app refuses the recursion before
# the usage measure can flag fun's double spend.
# ported from bend3: bare ctors, Num loses its U32 payload (unused)
type Term:
  Lam{bod: Term -> Term}
  App{fun: Term, arg: Term}
  Num{}

assert wnf:
  forall t: Term
  Term

def wnf(t):
  match t:
    case App{fun, arg}:
      match wnf(fun):
        case Lam{bod}:
          wnf(bod(fun))
        case f:
          App{f, arg}
    case t:
      t

assert main:
  Term

def main(): Num{}
$$ bend %
Error:
- expected : a decreasing self-call (some live argument must shrink)
- observed : wnf(bod(fun))
Context:
- fun : Term
- arg : Term
- bod : @_:Term -> Term
Location: wnf
19 |         case Lam{bod}:
20>|           wnf(bod(fun))
21 |         case f:
