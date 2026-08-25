# the textbook HOAS evaluator: beta is closure application, wnf feeds
# bod(arg), snf rebuilds under a fresh binder. bend3's linear-descent
# ledger certified this; bend4's descent law cannot (bod(arg) shrinks
# no column), so a Nat fuel rides ahead of every self-call (the
# queens shape) and the runtime pins survive: closures as ctor
# fields, capture, and the rebuilt-binder path.
# ported from bend3: bare ctors, the U32 answer reads back via
# U32.to_nat
import Base

type Trm:
  Lm{bod: Trm -> Trm}
  Ap{fun: Trm, arg: Trm}
  Nm{val: U32}

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
        case Ap{fun, arg}:
          match wnf(g, fun):
            case Lm{bod}:
              wnf(g, bod(arg))
            case h:
              Ap{h, arg}
        case t:
          t

assert snf:
  forall +f: +Nat
  forall t: Trm
  Trm

def snf(f, t):
  match f:
    case 0n:
      t
    case 1n+g:
      match wnf(g, t):
        case Lm{bod}:
          Lm{x => snf(g, bod(x))}
        case Ap{fun, arg}:
          Ap{snf(g, fun), snf(g, arg)}
        case t:
          t

assert main.out:
  Nat

def main.out():
  match snf(9n, Ap{Lm{x => Ap{Lm{y => y}, x}}, Nm{42}}):
    case Nm{val}:
      U32.to_nat(val)
    case t:
      0n

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
42n
$$ bend % --seq
42n
exit 0
$$ bend % --par
42n
exit 0
$$ bend % --js
42n
exit 0
