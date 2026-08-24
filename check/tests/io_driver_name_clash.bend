# io (io_driver_name_clash): the compiled-JS event loop's driver
# bindings live in a block scope of their own. A def compiles to the
# '$'-prefixed name, so defs named op and run emit $op and $run --
# the driver's own top-level `let $op` and `let $run` redeclared
# them, and the compiled program died at parse ("$run has already
# been declared") while the interpreter ran it: an output divergence
# between backends, the launch-blocker class of SPEC 1.8. The block
# makes the driver's names shadows, never redeclarations.
import Base

assert op:
  forall s: String
  String

def op(s):
  s ++ "!"

assert run:
  forall s: String
  IO(Unit)

def run(s):
  IO.print(op(s))

assert main:
  IO(Unit)

def main():
  do IO<Unit>:
    u : Unit <- run("driver")
    run("names")
$$ bend %
driver!
names!
$$ bend % --js
driver!
names!
exit 0
