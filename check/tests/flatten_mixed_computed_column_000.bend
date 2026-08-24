# a pattern column beside a computed value, in both orders; bend4's
# match takes bare scrutinees, so the value rides a var column (walk)
# or feeds a helper's pattern column (sel)
# ported from bend3: numerics become ctor columns (W), x+1 becomes the
# ctor build WS{x}, x%2 becomes a structural parity walk, literal arm
# values become ctors
type Nat:
  Z{}
  S{p: Nat}

type W:
  WZ{}
  WS{p: W}

type R:
  R1{}
  R2{}
  R3{}
  R4{}

assert par:
  forall x: W
  W

def par(x):
  match x:
    case WZ{}:
      WZ{}
    case WS{p}:
      match p:
        case WZ{}:
          WS{WZ{}}
        case WS{q}:
          par(q)

assert walk:
  forall n: Nat
  forall x: W
  W

def walk(n, x):
  match n, x:
    case Z{}, x:
      WS{x}
    case S{p}, x:
      walk(p, WS{x})

assert sel:
  forall k: W
  forall n: Nat
  R

def sel(k, n):
  match k, n:
    case WZ{}, Z{}:
      R1{}
    case WZ{}, S{p}:
      R2{}
    case k, Z{}:
      R3{}
    case k, S{p}:
      R4{}

assert main:
  forall x: W
  forall n: Nat
  R

def main(x, n):
  sel(par(x), n)
$$ bend % --show
par = \{WZ: WZ{}; WS: \{WZ: WS{WZ{}}; WS: (q => par(q))}}
walk = \{Z: (x => WS{x}); S: (p => x => walk(p, WS{x}))}
sel = \{WZ: \{Z: R1{}; S: (p => R2{})}; (k => \{Z: R3{}; S: (p => R4{})})}
main = x => n => sel(par(x), n)
