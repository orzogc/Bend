# a PURE main taking parameters is a COMPILE-time refusal: the compiled
# driver calls main with no arguments. The interpreter merely prints
# the stuck underapplied ref.
# ported from bend3
import Base

assert main:
  forall x: U32
  U32

def main(x):
  U32.add(x, 1)
$$ bend %
main
$$ bend % --seq
Error: tocl: main must answer IO<T>: the event loop runs IO mains only (report this case)
exit 1
