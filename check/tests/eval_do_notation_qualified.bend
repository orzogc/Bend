# a do-block's monad head may be a QUALIFIED (dotted) name: the desugar
# glues .bind/.pure onto the whole head (do M.Id<..>: -> M.Id.bind).
# ported from bend3: M.Id(A) becomes M.Id<A>, the bind spells its
# per-line type, result 42 shown as a Nat
import Base

type M.Id<A: Type>:
  MkMId{v: A}

assert M.Id.pure:
  forall -A: Type
  forall v: A
  M.Id<A>

def M.Id.pure(A, v):
  MkMId{v}

assert M.Id.bind:
  forall -A: Type
  forall -B: Type
  forall m: M.Id<A>
  forall f: @x:A -> M.Id<B>
  M.Id<B>

def M.Id.bind(A, B, m, f):
  match m:
    case MkMId{v}:
      f(v)

assert run:
  forall m: M.Id<U32>
  U32

def run(m):
  match m:
    case MkMId{v}:
      v

assert main.out:
  Nat

def main.out():
  U32.to_nat(run(do M.Id<U32>:
    x : U32 <- {MkMId{40} : M.Id<U32>}
    return U32.add(x, 2)))

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
