# SPEC PART 3 COP: an annotated dead value at a Copiable goal
# promotes to a live check (cop-wit), so an inline lambda hidden
# behind an erased let is refused exactly like the lambda spelled in
# the "~" position
import Base

type AuditDup<-T: Type>:
  AuditTwo{left: T, right: T}

assert audit_clone:
  forall -T: Type
  @x: T ->
  AuditDup<T>

def audit_clone(T, x):
  -w = {(
    z => Tuple{
      Tuple{z, {==}},
      Tuple{z, {==}}
    }
  ) : Copiable(T)}
  +y = {x : + T ~ w};
  AuditTwo{y, y}
$$ bend %
Error:
- expected : z
- observed : z (consumed more than once)
Context:
- T : Type
- x : T
Location: audit_clone
16 |   -w = {(
17>|     z => Tuple{
18 |       Tuple{z, {==}},
