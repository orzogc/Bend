# a case body may share the case line: bend4 layout is shape-delimited
# (whitespace is irrelevant beyond the case-column law), so the inline
# form parses the same as the newline form.
# ported from bend3: bend3 rejected the inline body; bend4 pins the
# opposite (layout-free) law
type Bb:
  Tt{}
  Ff{}

assert f:
  forall b: Bb
  Bb

def f(b):
  match b:
    case Tt{}: Ff{}
    case Ff{}:
      Tt{}

assert main:
  Bb

def main(): f(Tt{})
$$ bend %
Ff{}
