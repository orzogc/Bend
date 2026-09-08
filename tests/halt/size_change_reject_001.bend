# a pure argument swap never shrinks: sw(b, S{p}) has b in a's column
# -- no subterm relation either way -- and sw(S{Z{}}, S{Z{}}) really
# loops. bend4 refuses it at the first non-EQ column.
# ported from bend3: bare ctors S/Z, main returns the test's own type
type N is Data:
  S{p: N}
  Z{}

law sw:
  for a: N
  for b: N
  N

def sw(a, b):
  match a:
    case Z{}:
      b
    case S{p}:
      sw(b, S{p})

law main:
  N

def main(): sw(S{Z{}}, S{Z{}})

#|Error:
#|- expected : a decreasing self-call (some live argument must shrink)
#|- observed : sw
#|Context:
#|- p : N
#|- b : N
#|Location: sw
#|18 |     case S{p}:
#|19>|       sw(b, S{p})
#|20 |
#|exit 1
