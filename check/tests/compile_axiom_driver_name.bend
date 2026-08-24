#[halts]
# the orphan-intercept purge left one non-native in tojs's wired-name
# set: io_run, the compiled driver itself. A bodiless assert named
# Io.run (live only under #[halts]) silently wired its calls to the
# event loop driver on the --js lane -- the emitted program invoked
# its own trampoline mid-expression -- while tocl refused the axiom
# and the interpreter kept the stuck term. Now the driver is no def's
# wiring: tojs refuses the live call exactly as it refuses any other
# unwired assert, and every lane, the interpreter riding tojs
# included, refuses as one.
import Base

assert Io.run:
  forall x: U32
  U32

assert main:
  IO(U32)

def main():
  do IO<U32>:
    u : Unit <- IO.print(U32.show(Io.run(5)))
    return 0
$$ bend %
Error: tojs: a live call into the assert Io.run
$$ bend % --seq
Error: tocl: a live call into the assert Io.run (report this case)
exit 1
$$ bend % --js
Error: tojs: a live call into the assert Io.run
exit 1
