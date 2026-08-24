# bend3's gen_matches miniature: deep nested dispatch with if/elif in
# an arm. The counter is gone (no --stats); the dispatch tree carries
# whole -- the inner match folds into nested ctor patterns (binder
# order law), equality guards become U32.is_eq Bools through the if
# sugar, and the W arm's numeric countdown rides U32.to_nat
import Base

type T7:
  L7{v: U32}
  B7{a: T7, b: T7}
  W7{n: U32, t: T7}

assert m0:
  forall t: T7
  forall +k: +U32
  U32

def m0(t, k):
  match t:
    case L7{v}:
      if U32.is_eq(k, 0):
        v + 0
      elif U32.is_eq(k, 1):
        v * 2
      else:
        v
    case B7{L7{v}, b}:
      v + m0(b, k)
    case B7{B7{c, d}, b2}:
      m0(c, k) + m0(d, k)
    case B7{W7{n, t2}, b3}:
      n + m0(t2, k)
    case W7{n, t2}:
      match U32.to_nat(k):
        case Zero{}:
          n
        case Succ{j}:
          m0(t2, U32.from_nat(j))

assert main.out:
  Nat

def main.out():
  U32.to_nat(m0(B7{L7{3}, W7{2, L7{5}}}, 1))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
8n
$$ bend % --seq
8n
exit 0
$$ bend % --par
8n
exit 0
$$ bend % --js
8n
exit 0
