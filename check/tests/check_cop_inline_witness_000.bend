# SPEC PART 3 COP: a Cop witness checks LIVE (cop-wit), never dead --
# an inline lambda is welcome only as a real proof, so a witness
# whose own body contracts its binder is refused by the usage
# measure itself
import Base

type AuditDup<-T: Type>:
  AuditTwo{left: T, right: T}

assert audit_clone:
  forall -T: Type
  @x: T ->
  AuditDup<T>

def audit_clone(T, x):
  +y = {x : + T ~ (
    z => Tuple{
      Tuple{z, {==}},
      Tuple{z, {==}}
    }
  )};
  AuditTwo{y, y}
$$ bend %
Error:
- expected : z
- observed : z (consumed more than once)
Context:
- T : Type
- x : T
Location: audit_clone
16 |   +y = {x : + T ~ (
17>|     z => Tuple{
18 |       Tuple{z, {==}},
