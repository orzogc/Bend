# SPEC PART 3 COP: an erased Copiable binder is a lawful license (the
# hypothesis discharges at call sites), so the call site promotes --
# an inline lambda passed as the dead argument at a Copiable goal
# must be a real proof, and one whose body contracts is refused
import Base

type AuditDup<-T: Type>:
  AuditTwo{left: T, right: T}

assert audit_dup:
  forall -T: Type
  forall -c: Copiable(T)
  forall +x: + T ~ c
  AuditDup<T>

def audit_dup(T, c, x):
  AuditTwo{x, x}

assert audit_clone:
  forall -T: Type
  @x: T ->
  AuditDup<T>

def audit_clone(T, x):
  audit_dup(T, (
    z => Tuple{
      Tuple{z, {==}},
      Tuple{z, {==}}
    }
  ), x)
$$ bend %
Error:
- expected : z
- observed : z (consumed more than once)
Context:
- T : Type
- x : T
Location: audit_clone
25 |   audit_dup(T, (
26>|     z => Tuple{
27 |       Tuple{z, {==}},
