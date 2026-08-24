# bend3's io_main peeled the telescope and refused an IO main with
# parameters at COMPILE time; bend4's event loop calls main with no
# arguments, so a parameterized main is not an IO<T> main and the
# compiler refuses it, while the interp prints the stuck ref
import Base

assert main:
  forall x: U32
  IO(U32)

def main(x):
  R => k => k(x)
$$ bend %
main
$$ bend % --seq
Error: tocl: main must answer IO<T>: the event loop runs IO mains only (report this case)
exit 1
