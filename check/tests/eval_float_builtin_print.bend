# stuck float builtins print as their spelling under the open binders
# (F32 ops are base asserts: machine ops never reduce on open words;
# base-native asserts are live-usable strict).
# ported from bend3: bend4 has no float literals or operators, so the
# atan2 half drops and the ops spell F32.add/F32.sqrt; the reused y
# splits into two binders (a lambda binder is never Many)
import Base

assert main:
  @y:F32 -> @z:F32 -> F32

def main():
  y => z => F32.add(F32.sqrt(y), z)
$$ bend %
y => z => F32.add(F32.sqrt(y), z)

