# bend3's prep_unfold redex hideouts (a Lone let's literal lam, and
# statements commuting through value positions); bend4 has no such
# pass and the shapes simply evaluate -- the literal-ctor scrutinee
# routes through a def (a literal ctor may not be destructured in
# place), the lam let moves under the arm (a match heads a def body),
# and the value carries: 22
import Base

type B8r:
  B8r{a: U32}

assert use:
  forall f: U32 -> U32
  U32

def use(f):
  y = f(3)
  y + 1

assert mk:
  forall k: U32
  B8r

def mk(k):
  B8r{use(x => x * 2 + k)}

assert main.out:
  Nat

def main.out():
  match mk(0):
    case B8r{a}:
      h = {x => x + 1 : U32 -> U32}
      U32.to_nat(h(a) + use(x => x + 10))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
22n
$$ bend % --seq
22n
exit 0
$$ bend % --par
22n
exit 0
$$ bend % --js
22n
exit 0
