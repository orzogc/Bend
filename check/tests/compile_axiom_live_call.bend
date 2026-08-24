#[halts]
# a bodiless assert is an axiom: visible, stuck and dead-only, with a
# live call legal only under #[halts]. tocl always refused to compile
# one, but tojs consulted the runtime.js function names alone, so an
# axiom whose lowercased name matched an orphan intercept (nat_min and
# thirteen relatives survived base's 16k prune with no base def left)
# silently WIRED and ran on the --js lane while the C lane refused and
# the interpreter stayed stuck -- and an axiom matching nothing emitted
# a call to a function that never exists, a bare ReferenceError at
# runtime. Now the orphan intercepts are gone and tojs refuses a live
# call into any unwired assert at compile time, tocl's own reading; the
# interpreter compiles through tojs, so it refuses with the same line.
import Base

assert mystery:
  forall a: Nat
  Nat

assert main:
  IO(Unit)

def main():
  do IO<Unit>:
    IO.print(Nat.show(mystery(3n)))
$$ bend %
Error: tojs: a live call into the assert mystery
$$ bend % --seq
Error: tocl: a live call into the assert mystery (report this case)
exit 1
$$ bend % --js
Error: tojs: a live call into the assert mystery
exit 1
