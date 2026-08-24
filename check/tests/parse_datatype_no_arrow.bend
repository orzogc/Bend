# audit: a datatype header takes no arrow clause: `type K:` (or `type
# K<..>:`) is the only form, so `-> Type` fails at the arrow.
# ported from bend3: same law, bend4 error page
type Kk -> Type:
  Zz{}

assert main:
  Unit

def main(): Unit{}
$$ bend %
Error:
- expected : ':'
- observed : '-'
Location:
3 | # ported from bend3: same law, bend4 error page
4>| type Kk -> Type:
5 |   Zz{}
