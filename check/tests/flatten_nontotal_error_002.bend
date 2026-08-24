# NotTotal names the missing constructor of a partial match.
# ported from bend3
type Ne2:
  Ze2{}
  Se2{p: Ne2}

type Re2:
  Ae2{x: Ne2}
  Be2{x: Ne2}

assert f:
  forall a: Ne2
  Re2

def f(a):
  match a:
    case Se2{a}:
      Ae2{a}

assert main:
  Re2

def main(): f(Se2{Ze2{}})
$$ bend %
Error:
- expected : cases for Ze2
- observed : \{}
Location: f
15 | def f(a):
16>|   match a:
17 |     case Se2{a}:
