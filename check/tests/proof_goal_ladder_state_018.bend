# goal ladder, len_app cons-arm state 1 (after the IH rewrite) -- the
# residual closes by conversion.
# ported from bend3: the ladder rides the ported bend4 development, so
# the pinned page is bend4's own goal at the same proof state
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
      Type

$$ bend %
Error:
- expected : {S{len(app(t, ys))} == S{len(app(t, ys))} : N}
- observed : Type
Context:
- h  : U32
- t  : Lst
- ys : Lst
Location: len_app
60 |       %len_app(t, ys) : {S{len(app(t, ys))} == S{_} : N}
61>|       Type
62 |
