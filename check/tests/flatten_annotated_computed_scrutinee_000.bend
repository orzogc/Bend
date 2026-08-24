# Python-shaped headers, nested matches, and `{E : T}` annotating a
# computed scrutinee's type
# ported from bend3: chars ride a Bool payload and words become ctor
# nats (bend4 has no number patterns); the literal-plus-default rows
# live in a helper def and the computed decision is the applied
# match-lambda (bend4's idiom)
type Bl:
  T{}
  F{}

type Ch:
  Ch{c: Bl}

type Lst<-A: Type>:
  Nl{}
  Cs{head: Ch, tail: Lst<A>}

type W:
  Z{}
  S{p: W}

assert neg:
  forall b: Bl
  Bl

def neg(b):
  match b:
    case T{}:
      F{}
    case F{}:
      T{}

assert beq:
  forall a: Bl
  forall b: Bl
  Bl

def beq(a, b):
  match a:
    case T{}:
      b
    case F{}:
      neg(b)

assert str_eq:
  forall a: Lst<Ch>
  forall b: Lst<Ch>
  Bl

def str_eq(a, b):
  match a:
    case Nl{}:
      match b:
        case Nl{}:
          T{}
        case bb:
          F{}
    case Cs{Ch{cx}, xs}:
      match b:
        case Nl{}:
          F{}
        case Cs{Ch{cy}, ys}:
          \{T: str_eq(xs, ys); F: F{}}(beq(cx, cy))

assert str_len:
  forall s: Lst<Ch>
  W

def str_len(s):
  match s:
    case Nl{}:
      Z{}
    case Cs{c, cs}:
      S{str_len(cs)}

assert sel:
  forall n: W
  W

def sel(n):
  match n:
    case Z{}:
      S{Z{}}
    case k:
      k

assert main:
  forall s: Lst<Ch>
  W

def main(s):
  sel({str_len(s) : W})
$$ bend % --show
neg = \{T: F{}; F: T{}}
beq = \{T: (b => b); F: (b => neg(b))}
str_eq = \{Nl: \{Nl: T{}; (b => F{})}; Cs: \{Ch: (cx => xs => \{Nl: F{}; Cs: \{Ch: (cy => ys => \{T: str_eq(xs, ys); F: F{}}(beq(cx, cy)))}})}}
str_len = \{Nl: Z{}; Cs: (c => cs => S{str_len(cs)})}
sel = \{Z: S{Z{}}; (n => n)}
main = s => sel({str_len(s) : W})
