# destructure then MATCH an extracted field: the field binder from the
# destructure drives a later match statement
# ported from bend3: the matched field moves last (bend4's law: the
# scrutinee is the last-bound live binder -- leftovers first, decision
# last)
type Nt:
  Z{}
  S{p: Nt}

type Duo:
  P{a: Nt, b: Nt}

assert main:
  forall w: Duo
  Nt

def main(w):
  P{a, b} = w
  match b:
    case Z{}:
      a
    case S{p}:
      p
$$ bend % --show
main = \{P: (a => \{Z: a; S: (p => p)})}
