# bend3's term_subst fence, counter layer: the pure case-tree corpus
# rewrote NOTHING and subst_nodes pinned exact zero. The counter is
# gone (no --stats); the corpus itself carries -- the mul commutation
# closes by conversion alone, no rewrite spelled anywhere
import Base

type N8:
  Z8{}
  S8{p: N8}

assert N8.copy:
  forall t: N8
  Copy(N8, t) & Copy(N8, t)

def N8.copy(t):
  match t:
    case Z8{}:
      ((Z8{}, {==}), (Z8{}, {==}))
    case S8{p}:
      ((px, pe), (py, pf)) = N8.copy(p)
      s10 = Equal.cong(N8, N8, z => S8{z}, p, px, pe)
      s20 = Equal.cong(N8, N8, z => S8{z}, p, py, pf)
      ((S8{px}, s10), (S8{py}, s20))

assert add8:
  forall a: N8
  forall b: N8
  N8

def add8(a, b):
  match a:
    case Z8{}:
      b
    case S8{p}:
      S8{add8(p, b)}

assert mul8:
  forall a: N8
  forall +b: +N8
  N8

def mul8(a, b):
  match a:
    case Z8{}:
      Z8{}
    case S8{p}:
      add8(b, mul8(p, b))

assert m8:
  N8

def m8():
  S8{S8{S8{S8{S8{S8{S8{S8{Z8{}}}}}}}}}

assert m9:
  N8

def m9():
  S8{m8()}

assert cm:
  {mul8(m8(), m9()) == mul8(m9(), m8()) : N8}

def cm():
  {==}

assert main:
  N8

def main():
  Z8{}
$$ bend %
Z8{}
$$ bend % --js
Error: main must answer IO<T>
exit 1
