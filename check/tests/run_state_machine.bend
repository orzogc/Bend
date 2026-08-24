# a state machine at runtime: turnstile (Locked/Open) driven by an input
# list, counting passes and rejections; nested match dispatch per step
# ported from bend3: the multi-column match survives whole -- nested
# ctor patterns in the input column, the state beside it; strict, the
# continuation def folded away
import Base

type St:
  Locked{}
  Open{}

type In:
  Coin{}
  Push{}
  N{}
  C{i: In, t: In}

assert step:
  forall i: In
  forall s: St
  forall pass: U32
  forall rej: U32
  U32

def step(i, s, pass, rej):
  match i s:
    case N{} _:
      U32.add(U32.mul(pass, 10), rej)
    case C{Coin{}, t} _:
      step(t, Open{}, pass, rej)
    case C{Push{}, t} Open{}:
      step(t, Locked{}, U32.add(pass, 1), rej)
    case C{Push{}, t} Locked{}:
      step(t, Locked{}, pass, U32.add(rej, 1))
    case C{N{}, t} _:
      99
    case C{C{a, b}, t} _:
      99
    case Coin{} _:
      99
    case Push{} _:
      99

assert main.out:
  U32

def main.out():
  ins = {C{Push{}, C{Coin{}, C{Push{}, C{Coin{}, C{Coin{}, C{Push{}, N{}}}}}}} : In}
  step(ins, Locked{}, 0, 0)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
21
$$ bend % --seq
21
exit 0
$$ bend % --par
21
exit 0
$$ bend % --js
21
exit 0
