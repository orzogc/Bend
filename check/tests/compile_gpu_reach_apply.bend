# bend3 pinned the GPU program's dynamic-apply closure set by csrc
# marks; bend4's emitter has its own shapes, so the semantic half
# carries: a marked root taking a host-built partial application
# answers the plain call's value on every lane
import Base

assert cpu_only:
  forall x: U32
  U32

def cpu_only(x):
  x + 40

assert run:
  forall f: U32 -> U32
  forall x: U32
  U32

def run(f, x):
  f(x)

assert add2:
  forall a: U32
  forall b: U32
  U32

def add2(a, b):
  a + b

assert main.out:
  Nat

def main.out():
  x = cpu_only(0)
  U32.to_nat(run!(add2(2), x))

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
