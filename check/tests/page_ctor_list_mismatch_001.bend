# a case naming a constructor no datatype declares: the error names
# the case's tag (bend4 tags are global, so this is unknown-at-parse,
# never an internal flattened match)
type MB:
  T{}
  F{}
assert not:
  forall b: MB
  MB

def not(b):
  match b:
    case Tr{}:
      F{}
    case F{}:
      T{}
assert main:
  MB

def main(): not(T{})

$$ bend %
Error:
- message  : a declared constructor (unknown: Tr)
Location:
12 |   match b:
13>|     case Tr{}:
14 |       F{}
