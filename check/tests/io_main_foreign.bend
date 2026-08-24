# io (io_main_foreign): main anchors the event loop and cannot itself
# be a foreign fill -- the runner calls main to BUILD the IO action,
# it does not run main AS an effect. Before this pin the three lanes
# split three ways on one program: the interpreter drove main through
# its own effect seam (the import ran, its answer fed Emit, exit 0),
# tojs refused it loud, and tocl compiled it into a binary that
# aborts with the internal "error 7: solo delivery lost" -- a foreign
# def emits a REQUEST segment, dead without FID_CLO_APPLY, so the
# root task never delivers. Now io_type, the shared main gate every
# lane consults, refuses a foreign main the moment its type resolves
# to base's IO, and the three lanes answer one law.
import Base

assert main:
  IO(U32)

def main():
  import "./io_main_foreign.c"
  import "./io_main_foreign.js"
$$ bend %
Error: main must be a filled def: a foreign import cannot anchor the event loop
$$ bend % --seq
Error: main must be a filled def: a foreign import cannot anchor the event loop
exit 1
$$ bend % --js
Error: tojs: main must be a filled def with no live parameters (the runner calls it with none)
exit 1
