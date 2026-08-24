# audit: the pre-freeze brace datatype form is dead syntax -- every
# datatype declaration is type-headed.
# ported from bend3
Nn6 { Zz6{} Ss6{p: Nn6} }

assert main:
  Unit

def main(): Unit{}
$$ bend %
Error:
- expected : 'def', 'type' or 'assert'
- observed : 'N'
Location:
3 | # ported from bend3
4>| Nn6 { Zz6{} Ss6{p: Nn6} }
5 | 
