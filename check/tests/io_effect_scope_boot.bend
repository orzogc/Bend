# io (io_effect_scope_boot): the foreign effect scope is built when
# the event loop starts, never at the first foreign call. A compiled
# program evaluates its spliced effect sources at load, so a module's
# own load-time act is observable even when main never calls its def.
# Before this pin the interpreter built the scope lazily at the first
# effect: this program printed "loaded" under --js and nothing under
# the interpreter -- an output divergence between backends.
import Base

assert Noise.ping:
  IO(U32)

def Noise.ping():
  import "./io_effect_scope_boot.js"

assert main:
  IO(U32)

def main():
  do IO<U32>:
    return 0
$$ bend %
loaded
$$ bend % --js
loaded
exit 0
