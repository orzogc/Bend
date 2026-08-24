# the do-desugared bind/pure calls carry the statement's span, so a
# missing monad def reports the offending line, not a bare def name
# (AUDIT 6c: do-notation desugaring lost the reporting node's span).
import Base

type Box:
  Mk{v: U32}

assert main:
  Box

def main():
  do Box<>:
    x : U32 <- Mk{3}
    return x
$$ bend %
Error:
- expected : a defined name
- observed : Box.bind
Location: main
13 |   do Box<>:
14>|     x : U32 <- Mk{3}
15 |     return x
