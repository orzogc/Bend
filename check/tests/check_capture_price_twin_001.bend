# computed-match twin: the scrutinee is a call, the hypothesis h
# mentions it, and the binder k still measures at the branch join --
# computed and variable matches price identically.
# ported from bend3: bend4 statement-lets cannot precede a match, so k
# spends inside the arms
type Ne:
  Ze{}
  Se{p: Ne}

assert fe:
  forall n: Ne
  Ne

def fe(n):
  match n:
    case Ze{}:
      Ze{}
    case Se{p}:
      Se{p}

assert use:
  forall n: Ne
  forall h: {fe(n) == Ze{} : Ne}
  forall k: Ne -> Ne
  Ne

def use(n, h, k):
  match fe(n):
    case Ze{}:
      k(Ze{})
    case Se{p}:
      k(Se{p})

assert main:
  Ne

def main():
  Ze{}
$$ bend %
Ze{}
