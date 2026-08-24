# theorems: length-append over a local list -- structural induction on
# one ADT proving an equation whose carrier is another (N).
# ported from bend3: local Nat/Lst renamed off base's ctor namespace;
# the IH rewrite carries its explicit motive
import Base

type N:
  Z{}
  S{p: N}

type Lst:
  LNil{}
  LCon{h: U32, t: Lst}

assert add:
  forall a: N
  forall b: N
  N

def add(a, b):
  match a:
    case Z{}:
      b
    case S{p}:
      S{add(p, b)}

assert len:
  forall xs: Lst
  N

def len(xs):
  match xs:
    case LNil{}:
      Z{}
    case LCon{h, t}:
      S{len(t)}

assert app:
  forall xs: Lst
  forall ys: Lst
  Lst

def app(xs, ys):
  match xs:
    case LNil{}:
      ys
    case LCon{h, t}:
      LCon{h, app(t, ys)}

assert len_app:
  forall xs: Lst
  forall ys: Lst
  {len(app(xs, ys)) == add(len(xs), len(ys)) : N}

def len_app(xs, ys):
  match xs:
    case LNil{}:
      {==}
    case LCon{h, t}:
      %len_app(t, ys) : {S{len(app(t, ys))} == S{_} : N}
      {==}

assert main:
  {len(app(LCon{1, LNil{}}, LCon{2, LCon{3, LNil{}}})) == S{S{S{Z{}}}} : N}

def main(): len_app(LCon{1, LNil{}}, LCon{2, LCon{3, LNil{}}})

$$ bend %
{==}
