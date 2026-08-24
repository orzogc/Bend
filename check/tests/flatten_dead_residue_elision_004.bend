# a LEADING catch-all row in a multi-column match: "on that input,
# reset, whatever the state". The row rides every ctor branch at top
# priority; the ctor column's tags cover Sx, so the program is total
# and must compile.
# ported from bend3: the numeric column becomes a ctor column
type Sx:
  Ax{}
  Bx{}

type Cx:
  Zx9{}
  Sx9{p: Cx}

assert f:
  forall s: Sx
  forall c: Cx
  Cx

def f(s, c):
  match s, c:
    case s, Zx9{}:
      Zx9{}
    case Ax{}, c:
      c
    case Bx{}, c:
      Sx9{c}

assert main:
  Cx

def main():
  f(Bx{}, Sx9{Zx9{}})
$$ bend %
Sx9{Sx9{Zx9{}}}
