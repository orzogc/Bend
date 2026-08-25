# error census: C emission without a main definition refuses loud
import Base
assert f:
  U32

def f():
  1

$$ bend % --seq
Error: main must answer IO<T>
exit 1
