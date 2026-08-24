# SPEC PART 3: the trailing-dot family (+. -. *. /. ==. !=. <=. >=.
# <. >.) is the one float spelling -- the old dotted-both-sides .+.
# dies at its leading dot, which no infix owns
import Base

assert main:
  F32

def main():
  1.0 .+. 2.0
$$ bend %
Error:
- expected : 'def', 'type' or 'assert'
- observed : '.'
Location:
 9 | def main():
10>|   1.0 .+. 2.0
11 |
