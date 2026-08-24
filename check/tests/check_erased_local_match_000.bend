# AUDIT 17, residual claim: body_flatten must carry an erased local's
# quantity even when the body is a MATCH - the None binder reaches the
# checker and the live use is refused (AUDIT 4a's repair, match shape)
type Bit:
  On{}
  Off{}

assert erase_then_match:
  forall z: Bit
  Bit

def erase_then_match(z):
  -x = {z : Bit}
  match x:
    case On{}: On{}
    case Off{}: Off{}
$$ bend %
Error:
- expected : -x
- observed : x
Context:
- z : Bit
Location: erase_then_match
12 | def erase_then_match(z):
13>|   -x = {z : Bit}
14 |   match x:
