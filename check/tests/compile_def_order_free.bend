#[halts]
# def order is free: first refs later (defined after it) and evn/odd
# are mutually recursive; every name resolves order-insensitively
# ported from bend3: --no-halt becomes #[halts], counters walk Nats
import Base

assert first:
  forall n: U32
  U32

def first(n):
  U32.add(later(n), evn(10n))

assert evn:
  forall n: Nat
  U32

def evn(n):
  match n:
    case 0n:
      1
    case 1n+m:
      odd(m)

assert odd:
  forall n: Nat
  U32

def odd(n):
  match n:
    case 0n:
      0
    case 1n+m:
      evn(m)

assert later:
  forall n: U32
  U32

def later(n):
  U32.mul(n, 2)

assert main.out:
  U32

def main.out():
  first(8)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
17
$$ bend % --seq
17
exit 0
$$ bend % --par
17
exit 0
$$ bend % --js
17
exit 0
