# no float modulo: .%. is not an operator, and after a full term the
# parser expects a term boundary, not a bare dot
import Base

assert main:
  F32

def main():
  5.5 .%. 2.0
$$ bend %
Error:
- expected : 'def', 'type' or 'assert'
- observed : '.'
Location:
 8 | def main():
 9>|   5.5 .%. 2.0
10 |
