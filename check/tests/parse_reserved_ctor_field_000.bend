# audit 024: reserved names cannot be used as constructor fields.
# ported from bend3
type Kk8:
  Mk8{Type: Kk8}

assert main:
  Kk8

def main(): Mk8{}
$$ bend %
Error:
- expected : a name (got the keyword 'Type')
- observed : ':'
Location:
3 | type Kk8:
4>|   Mk8{Type: Kk8}
5 | 
