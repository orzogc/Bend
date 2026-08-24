# a monadic loop through continuation lambdas: a bind whose
# continuation ends in the self-recursive call, threading context
# through the closure -- and the descent judgment sees the self-call
# through the bind's lambda (no #[halts] anywhere: the recursion
# descends, and the shared fd takes +U32, a Cop).
# ported from bend3: IO becomes base Result, the counter becomes Nat
# fuel; the bend3 arm's inner match and let cannot ride a do block
# (match heads a def body; DoLet never parses -- io_do_let_lines pins
# that), so the continuation folds the let into the tail call
import Base

assert nod:
  forall fd: U32
  forall x: U32
  Result<U32, U32>

def nod(fd, x):
  Done{U32.add(fd, x)}

assert rec:
  forall +fd: +U32
  forall n: Nat
  forall len: U32
  Result<U32, U32>

def rec(fd, n, len):
  match n:
    case 0n:
      Done{len}
    case 1n+m:
      do Result<U32, U32>:
        a : U32 <- nod(fd, 1)
        rec(fd, m, U32.add(len, a))

assert unwrap:
  forall r: Result<U32, U32>
  U32

def unwrap(r):
  match r:
    case Done{v}:
      v
    case Fail{x}:
      x

assert main.out:
  Nat

def main.out():
  U32.to_nat(unwrap(rec(7, 3n, 0)))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
24n
$$ bend % --seq
24n
exit 0
$$ bend % --par
24n
exit 0
$$ bend % --js
24n
exit 0
