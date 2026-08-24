# contraction is growth: bend3's NSI ledger refused loop because
# append(p, p) doubles what the match released. bend4 counts the same
# fact at the binder itself: p is affine, so its second spend in
# append(p, p) is refused in grow before loop is even reached.
# ported from bend3: bare ctors, main returns the test's own type
type T:
  S{p: T}
  Z{}

assert append:
  forall a: T
  forall b: T
  T

def append(a, b):
  match b:
    case S{q}:
      S{append(a, q)}
    case b:
      a

assert grow:
  forall t: T
  T

def grow(t):
  match t:
    case S{p}:
      S{append(p, p)}
    case t:
      t

assert loop:
  forall t: T
  T

def loop(t):
  match grow(t):
    case S{x}:
      loop(x)
    case w:
      w

assert main:
  T

def main(): Z{}
$$ bend %
Error:
- expected : p
- observed : p (consumed more than once)
Location: grow
27 |   match t:
28>|     case S{p}:
29 |       S{append(p, p)}
