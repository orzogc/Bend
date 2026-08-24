# a match-lambda applied to a constructor scrutinee cannot infer: the
# application needs an annotation.
# ported from bend3
type Nx5:
  Zx5{}
  Sx5{p: Nx5}

type Rx5:
  Ax5{x: Nx5}
  Bx5{y: Nx5}

assert main:
  Rx5

def main(): (\{Zx5: Bx5{Zx5{}}; Sx5: x => Ax5{x}})(Zx5{})
$$ bend %
Error:
- expected : an annotated term (cannot infer)
- observed : Zx5{}
Location: main
14 | 
15>| def main(): (\{Zx5: Bx5{Zx5{}}; Sx5: x => Ax5{x}})(Zx5{})
16 |
