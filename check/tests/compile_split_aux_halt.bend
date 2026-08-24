# recursion under nested split auxes with a contracted default binder
# ported from bend3: counters walk Nats, the shared peel becomes a
# +scrutinee
import Base

type Bl:
  Tt{}
  Ff{}

assert notb:
  forall a: Bl
  Bl

def notb(a):
  match a:
    case Tt{}:
      Ff{}
    case Ff{}:
      Tt{}

assert par:
  forall a: Nat
  Bl

def par(a):
  match a:
    case 0n:
      Tt{}
    case 1n+n2:
      notb(par(n2))

assert run:
  forall +n: +Nat
  U32

def run(n):
  match n:
    case 0n:
      0
    case 1n+n2:
      match par(n2):
        case Tt{}:
          match par(n2):
            case Tt{}:
              U32.add(1, run(n2))
            case Ff{}:
              0
        case Ff{}:
          run(n2)

assert main.out:
  U32

def main.out():
  U32.add(run(2n), U32.add(run(1n), run(3n)))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
4
$$ bend % --seq
4
exit 0
$$ bend % --par
4
exit 0
$$ bend % --js
4
exit 0
