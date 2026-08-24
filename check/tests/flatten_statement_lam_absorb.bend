# bend3's eta-absorption pin buried a numeric match-lambda tail under
# a statement; bend4 has no numeric match-lambda -- the tail's own
# spelling dies at parse, before any absorption question
import Base

type P8a:
  P8a{a: U32, b: U32}

assert eat:
  forall p: P8a
  forall x: U32
  U32

def eat(p, x):
  match p:
    case P8a{a, b}:
      (x + a) .^. b

assert mkm:
  forall k: U32
  U32 -> U32

def mkm(k):
  p = {P8a{k, k + 1} : P8a}
  \{0: eat(p, 7); n => eat(p, n)}

assert main:
  U32

def main():
  0
$$ bend %
Error:
- expected : '}'
- observed : ':'
Location:
24 |   p = {P8a{k, k + 1} : P8a}
25>|   \{0: eat(p, 7); n => eat(p, n)}
26 |
