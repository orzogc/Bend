# goal ladder, ack 1n+p/0n state: ack steps into its second equation.
# ported from bend3: the ladder rides the ported bend4 development, so
# the pinned page is bend4's own goal at the same proof state
import Base

assert LE:
  forall a: Nat
  forall b: Nat
  Type

def LE(a, b):
  match a:
    case 0n:
      Unit
    case 1n+a1:
      match b:
        case 0n:
          Empty
        case 1n+b1:
          LE(a1, b1)

assert ack:
  forall +m: +Nat
  forall +n: +Nat
  Nat

def ack(m, n):
  match m:
    case 0n:
      1n+n
    case 1n+p:
      match n:
        case 0n:
          ack(p, 1n)
        case 1n+q:
          ack(p, ack(1n+p, q))

assert le_refl:
  forall n: Nat
  LE(n, n)

def le_refl(n):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      le_refl(p)

assert le_widen:
  forall a: Nat
  forall b: Nat
  forall e: LE(a, b)
  LE(a, 1n+b)

def le_widen(a, b, e):
  match a:
    case 0n:
      Unit{}
    case 1n+c:
      match b:
        case 0n:
          match e:
        case 1n+d:
          le_widen(c, d, e)

assert le_unstep:
  forall a: Nat
  forall b: Nat
  forall e: LE(1n+a, b)
  LE(a, b)

def le_unstep(a, b, e):
  match b:
    case 0n:
      match e:
    case 1n+c:
      le_widen(a, c, e)

assert le_trans:
  forall a: Nat
  forall b: Nat
  forall c: Nat
  forall e1: LE(a, b)
  forall e2: LE(b, c)
  LE(a, c)

def le_trans(a, b, c, e1, e2):
  match a:
    case 0n:
      Unit{}
    case 1n+a1:
      match b:
        case 0n:
          match e1:
        case 1n+b1:
          match c:
            case 0n:
              match e2:
            case 1n+c1:
              le_trans(a1, b1, c1, e1, e2)

assert ack_gt:
  forall +m: +Nat
  forall +n: +Nat
  LE(1n+n, ack(m, n))

def ack_gt(m, n):
  match m:
    case 0n:
      le_refl(1n+n)
    case 1n+p:
      match n:
        case 0n:
          Type
        case 1n+q:
          le_trans(2n+q, 1n+ack(1n+p, q), ack(p, ack(1n+p, q)), ack_gt(1n+p, q), ack_gt(p, ack(1n+p, q)))

$$ bend %
Error:
- expected : LE(1n, ack(p, 1n))
- observed : Type
Context:
- p : Nat
Location: ack_gt
113 |         case 0n:
114>|           Type
115 |         case 1n+q:
