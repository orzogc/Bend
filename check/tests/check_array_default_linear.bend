# slab-array pin (check_array_default_linear): bend3 rejected a linear
# variable as an array default (a served default would duplicate it).
# bend4 has no array literals -- the ![ spelling pins bend4's own
# parse refusal.
import Base

type Token:
  TokA{f: U32 -> U32}
  TokB{}

type TPair<-E: Type>:
  TP{x: E, y: E}

assert dupt:
  forall x: Token
  TPair<Token>

def dupt(x):
  old = ![_:x; 1]@buf[0] <- TokB{}
  other = buf@rest[1]
  TP{old, other}

assert main:
  U32

def main():
  0
$$ bend %
Error:
- expected : a term
- observed : '!'
Location:
18 | def dupt(x):
19>|   old = ![_:x; 1]@buf[0] <- TokB{}
20 |   other = buf@rest[1]
