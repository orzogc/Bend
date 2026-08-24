# a constructor scrutinee, unannotated: whatever bend4 rules for the
# bare applied match over a build is pinned here (bend3 reduced it)
type Nt:
  Zn{}
  Sn{p: Nt}

type W:
  Z{}
  S{p: W}

assert f:
  forall n: Nt
  W

def f(n):
  \{Sn: (k => Z{})}(Sn{n})

assert main:
  W

def main():
  Z{}
$$ bend % --show f
Error:
- expected : an annotated term (cannot infer)
- observed : Sn{n}
Context:
- n : Nt
Location: f
15 | def f(n):
16>|   \{Sn: (k => Z{})}(Sn{n})
17 |
