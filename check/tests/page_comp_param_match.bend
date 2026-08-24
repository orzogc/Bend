# comp pin (page_comp_param_match): bend3's template body matching on
# its ~ param died at spec mint with the cannot-be-matched-on page.
# bend4 has no ~ params to mint; the ~ binder pins bend4's own parse
# refusal before any match is reached.
import Base

assert t:
  forall ~f: U32 -> U32
  U32

def t(f):
  match f:
    case U32{w}:
      0

assert main:
  U32

def main():
  t(x => x + 1)
$$ bend %
Error:
- expected : a name
- observed : '~'
Location:
7 | assert t:
8>|   forall ~f: U32 -> U32
9 |   U32
