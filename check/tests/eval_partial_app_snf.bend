#[halts]
# bend3's under-binder normalization of a partial application had no
# stable golden here once (the trusted HOAS normalizer overflowed the
# host); bend4's iterative print path renders it deterministically --
# the rebuilt binders carry their deferred snf thunk spelled as the
# bare stuck call, bend4's own shape
import Base

type Trm:
  TLam{bod: Trm -> Trm}
  TApp{fun: Trm, arg: Trm}
  TNum{val: U32}

assert wnf:
  forall t: Trm
  Trm

def wnf(t):
  match t:
    case TApp{fun, arg}:
      match wnf(fun):
        case TLam{bod}:
          wnf(bod(arg))
        case f:
          TApp{f, arg}
    case t:
      t

assert snf9:
  forall t: Trm
  Trm

def snf9(t):
  match wnf(t):
    case TLam{bod}:
      TLam{x => snf9(bod(x))}
    case TApp{fun, arg}:
      TApp{snf9(fun), snf9(arg)}
    case t:
      t

assert compose:
  Trm

def compose():
  TLam{f => TLam{g => TLam{x => TApp{f, TApp{g, x}}}}}

assert main:
  Trm

def main():
  snf9(TApp{compose(), TLam{y => y}})
$$ bend %
TLam{x => TLam{x => snf9(TApp{TLam{y => y}, TApp{x^0, x}})}}
