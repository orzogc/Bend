#[halts]
# the textbook HOAS evaluator: beta is closure application, wnf feeds
# bod(arg), snf rebuilds under a fresh binder. bend3's linear-descent
# ledger certified this; bend4's descent law cannot (bod(arg) shrinks
# no column), so the file opts out via #[halts] and pins the runtime:
# closures as ctor fields, capture, and the rebuilt-binder path.
# ported from bend3: bare ctors, the U32 answer reads back via
# U32.to_nat
import Base

type Trm:
  Lm{bod: Trm -> Trm}
  Ap{fun: Trm, arg: Trm}
  Nm{val: U32}

assert wnf:
  forall t: Trm
  Trm

def wnf(t):
  match t:
    case Ap{fun, arg}:
      match wnf(fun):
        case Lm{bod}:
          wnf(bod(arg))
        case f:
          Ap{f, arg}
    case t:
      t

assert snf:
  forall t: Trm
  Trm

def snf(t):
  match wnf(t):
    case Lm{bod}:
      Lm{x => snf(bod(x))}
    case Ap{fun, arg}:
      Ap{snf(fun), snf(arg)}
    case t:
      t

assert main.out:
  Nat

def main.out():
  match snf(Ap{Lm{x => Ap{Lm{y => y}, x}}, Nm{42}}):
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
