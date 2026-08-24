# compound-scrutinee ladder, complete: splitting n computes the cut
# away in both arms (wob's computed match add(n, Z{}) reduces per arm)
# ported from bend3: no pre-split rewrite -- a bend4 match heads a def
# body, so the split comes first, and both arms then close by {==}
type MN:
  Z{}
  S{p: MN}

assert add:
  forall a: MN
  forall b: MN
  MN

def add(a, b):
  match a:
    case Z{}:
      b
    case S{p}:
      S{add(p, b)}

assert wob:
  forall n: MN
  MN

def wob(n):
  match add(n, Z{}):
    case Z{}:
      Z{}
    case S{p}:
      S{p}

assert wob_id:
  forall n: MN
  {wob(n) == add(n, Z{}) : MN}

def wob_id(n):
  match n:
    case Z{}:
      {==}
    case S{p}:
      {==}

assert main:
  @n: MN -> {wob(n) == add(n, Z{}) : MN}

def main():
  n => wob_id(n)

$$ bend %
n => wob_id(n)
