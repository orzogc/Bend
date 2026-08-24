# bend3's harness-cache adversary, stats side: --stats bypassed the
# cache and measured a fresh check. bend4 has no --stats; the cache
# half that still speaks is pinned -- the rendered page and the value
# repeat byte-identically around each other off one in-process book
import Base

assert flip:
  forall c: Cmp
  Cmp

def flip(c):
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

assert main:
  Cmp

def main():
  flip(flip(LT{}))
$$ bend %
LT{}
$$ bend % --show flip
flip = \{LT: GT{}; EQ: EQ{}; GT: LT{}}
$$ bend %
LT{}
$$ bend % --show flip
flip = \{LT: GT{}; EQ: EQ{}; GT: LT{}}
