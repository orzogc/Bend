# red-team pin: reserved keywords are rejected as ctor FIELD names (a
# field is a binder).
# ported from bend3
type Kk9:
  Mk9{match: Unit}

assert main:
  Unit

def main(): Unit{}
$$ bend %
Error:
- expected : a name (got the keyword 'match')
- observed : ':'
Location:
4 | type Kk9:
5>|   Mk9{match: Unit}
6 | 
