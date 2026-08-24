# bend3's checker work pin (interactions under a flat budget) loses its
# counter (no --stats) and keeps its content: the same Nat kit, the
# add_zero ladder and the mul(8,9) == mul(9,8) conversion all close on
# bend4's checker (mul's contracted operand rides a + binder)
import Base

type N7:
  Z7{}
  S7{p: N7}

assert N7.copy:
  forall t: N7
  Copy(N7, t) & Copy(N7, t)

def N7.copy(t):
  match t:
    case Z7{}:
      ((Z7{}, {==}), (Z7{}, {==}))
    case S7{p}:
      ((px, pe), (py, pf)) = N7.copy(p)
      s10 = Equal.cong(N7, N7, z => S7{z}, p, px, pe)
      s20 = Equal.cong(N7, N7, z => S7{z}, p, py, pf)
      ((S7{px}, s10), (S7{py}, s20))

assert add7:
  forall a: N7
  forall b: N7
  N7

def add7(a, b):
  match a:
    case Z7{}:
      b
    case S7{p}:
      S7{add7(p, b)}

assert mul7:
  forall a: N7
  forall +b: +N7
  N7

def mul7(a, b):
  match a:
    case Z7{}:
      Z7{}
    case S7{p}:
      add7(b, mul7(p, b))

assert add_zero7:
  forall a: N7
  {add7(a, Z7{}) == a : N7}

def add_zero7(a):
  match a:
    case Z7{}:
      {==}
    case S7{p}:
      %add_zero7(p) : {S7{add7(p, Z7{})} == S7{_} : N7}
      {==}

assert n8:
  N7

def n8():
  S7{S7{S7{S7{S7{S7{S7{S7{Z7{}}}}}}}}}

assert n9:
  N7

def n9():
  S7{n8()}

assert cm:
  {mul7(n8(), n9()) == mul7(n9(), n8()) : N7}

def cm():
  {==}

assert main:
  N7

def main():
  Z7{}
$$ bend %
Z7{}
$$ bend % --js
Error: tojs: main must answer IO<T>: the event loop runs IO mains only
exit 1
