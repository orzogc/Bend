# a pure argument swap never shrinks: sw(b, S{p}) has b in a's column
# -- no subterm relation either way -- and sw(S{Z{}}, S{Z{}}) really
# loops. bend4 refuses it at the first non-EQ column.
# ported from bend3: bare ctors S/Z, main returns the test's own type
type N:
  S{p: N}
  Z{}

assert sw:
  forall a: N
  forall b: N
  N

def sw(a, b):
  match a:
    case Z{}:
      b
    case S{p}:
      sw(b, S{p})

assert main:
  N

def main(): sw(S{Z{}}, S{Z{}})
$$ bend %
Error:
- expected : a decreasing self-call (some live argument must shrink)
- observed : sw(b, S{p})
Context:
- p : N
- b : N
Location: sw
18 |     case S{p}:
19>|       sw(b, S{p})
20 |
