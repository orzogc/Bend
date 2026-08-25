# bend3's under-binder normalization of a partial application had no
# stable golden here once (the trusted HOAS normalizer overflowed the
# host); bend4's iterative print path renders it deterministically --
# the rebuilt binders carry their deferred snf thunk spelled as the
# bare stuck call, bend4's own shape. The evaluator's recursion rides
# a Nat fuel matched ahead of every self-call (the queens shape); the
# thunk sticks where wnf matches a free variable, fuel in hand.
import Base

type Trm:
  TLam{bod: Trm -> Trm}
  TApp{fun: Trm, arg: Trm}
  TNum{val: U32}

assert wnf:
  forall +f: +Nat
  forall t: Trm
  Trm

def wnf(f, t):
  match f:
    case 0n:
      t
    case 1n+g:
      match t:
        case TApp{fun, arg}:
          match wnf(g, fun):
            case TLam{bod}:
              wnf(g, bod(arg))
            case h:
              TApp{h, arg}
        case t:
          t

assert snf9:
  forall +f: +Nat
  forall t: Trm
  Trm

def snf9(f, t):
  match f:
    case 0n:
      t
    case 1n+g:
      match wnf(g, t):
        case TLam{bod}:
          TLam{x => snf9(g, bod(x))}
        case TApp{fun, arg}:
          TApp{snf9(g, fun), snf9(g, arg)}
        case t:
          t

assert compose:
  Trm

def compose():
  TLam{f => TLam{g => TLam{x => TApp{f, TApp{g, x}}}}}

assert main:
  Trm

def main():
  snf9(9n, TApp{compose(), TLam{y => y}})
$$ bend %
TLam{x => TLam{x => snf9(7n, TApp{TLam{y => y}, TApp{x^0, x}})}}
