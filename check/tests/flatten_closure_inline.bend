# bend3's term_leaf closure-inlining pin (partial applications of
# known defs collapsing to direct calls); bend4's compiler has no such
# pass, so the SHAPES carry as plain closures: the boundary return,
# the curried 2-stage chain, multi-arm consumption, the escaping
# partial and the bare def reference all evaluate -- countdowns ride
# Nat with a U32 mirror, dispatch guards ride is_eq (word views stay
# out of tocl), contraction rides +Nat/+U32 (Cop) binders; the count
# is 8, not bend3's 1000: the interp re-forces the acc chain (the
# class cost_stuck_chain_compact pins as the suite's yellow) and goes
# exponential past ~10
import Base

assert mk:
  forall +i: +U32
  U32 -> U32

def mk(i):
  match U32.is_eq(i .&. 1, 0):
    case True{}:
      x => x + (i * 3)
    case False{}:
      x => x .^. (i << 2n)

assert mk2:
  forall +a: +U32
  U32 -> U32 -> U32

def mk2(a):
  x => y => (x * a) + (y .^. a)

assert use:
  forall f: U32 -> U32
  forall x: U32
  U32

def use(f, x):
  f(x)

assert go2:
  forall n: Nat
  forall +i: +U32
  forall acc: U32
  U32

def go2(n, i, acc):
  match n:
    case Zero{}:
      acc
    case Succ{k}:
      f = mk2(i)
      g = f(acc)
      go2(k, i - 1, g(7))

assert arms:
  forall b: U32
  forall i: U32
  U32

def arms(b, i):
  match U32.is_eq(b .&. 1, 0):
    case True{}:
      f = mk(i)
      f(10)
    case False{}:
      f = mk(i)
      f(20)

assert esc:
  forall i: U32
  U32

def esc(i):
  f = mk(i)
  use(f, 5)

assert bare:
  forall i: U32
  U32

def bare(i):
  f = {mk : @+z:+U32 -> U32 -> U32}
  f(i, 9)

assert main.out:
  Nat

def main.out():
  U32.to_nat(go2(8n, 8, 3) + ((arms(2, 7) + arms(3, 8)) + (esc(11) + bare(6))))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
196899n
$$ bend % --seq
196899n
exit 0
$$ bend % --par
196899n
exit 0
$$ bend % --js
196899n
exit 0
