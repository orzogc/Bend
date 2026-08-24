# the C showable wall: a user constructor is not a C result -- SPEC
# 1.8 prints one result String, and tocl refuses a main whose answer
# it cannot show, loud. The interpreter and the JS backend print the
# ctor spine.
# ported from bend3: bend3's tag-punned improper-chain readback
# (1<>2) is bend3-only; the pin here is bend4's refusal on the same
# shape, plus the interp/js spellings (Nat fields for readability)
import Base

type Chain:
  ChCons{h: Nat, t: Nat}

assert main:
  Chain

def main():
  ChCons{1n, 2n}
$$ bend %
ChCons{1n, 2n}
$$ bend % --seq
Error: tocl: main must answer IO<T>: the event loop runs IO mains only (report this case)
exit 1
$$ bend % --par
Error: tocl: main must answer IO<T>: the event loop runs IO mains only (report this case)
exit 1
$$ bend % --js
Error: tojs: main must answer IO<T>: the event loop runs IO mains only
exit 1
