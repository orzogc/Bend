# error census: C emission without a main definition refuses loud
import Base
assert f:
  U32

def f():
  1

$$ bend % --seq
Error: tocl: main must answer IO<T>: the event loop runs IO mains only (report this case)
exit 1
