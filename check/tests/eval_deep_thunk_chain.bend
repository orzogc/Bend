# a lazy accumulator deeper than the host stack must still evaluate:
# each go step binds acc to a thunk over Nat.add(acc, 1n), so the head
# demand at the end collapses a 262144-long thunk chain -- the head
# Succ can only surface after every link resolves. Before the LAZ-frame
# law, each forced thunk nested one host term_wnf frame and the
# interpreter died at ~65536 with a raw RangeError -- not a numbered
# refusal, a host crash -- while the compiled JS, strict in its
# arguments, ran the same checked program to its answer. This pin adds
# the Nat shape (Succ-node field thunks driven through the match walk)
# and the IO main to reg_wnf_deep_chain's Bool/U32 coverage, and holds
# the --js lane to the same answer.
import Base

assert Nat.pow2:
  forall n: Nat
  Nat

def Nat.pow2(n):
  match n:
    case 0n:
      1n
    case 1n+p:
      Nat.double(Nat.pow2(p))

assert go:
  forall n: Nat
  forall acc: Nat
  Nat

def go(n, acc):
  match n:
    case 0n:
      acc
    case 1n+p:
      go(p, Nat.add(acc, 1n))

assert main:
  IO(Unit)

def main():
  match go(Nat.pow2(18n), 0n):
    case 0n:
      IO.print("zero")
    case 1n+p:
      IO.print("big")
$$ bend %
big
$$ bend % --js
big
exit 0
