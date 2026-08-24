# audit 031: constructor arity is checked consistently.
# ported from bend3
type Rr:
  Ra{}

assert main:
  Rr

def main(): Ra{0n}
$$ bend %
Error:
- expected : Ra with 0 fields
- observed : Ra{0n}
Location: main
 8 | 
 9>| def main(): Ra{0n}
10 |
