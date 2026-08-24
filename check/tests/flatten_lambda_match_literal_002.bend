# per-branch arity: the T arm takes one more argument; a \-match
# literal's arm bodies are plain terms, so the extra lambda just checks
# ported from bend3: bend4's All binds a name (the family applies to it
# explicitly), the inner computed numeric match becomes an applied
# match-lambda on the extra binder
type Bl:
  T{}
  F{}

type W:
  Z{}
  S{p: W}

assert main:
  @b: Bl -> \{T: @x: W -> W; F: W}(b)

def main():
  \{
    T: (x => \{Z: S{Z{}}; S: (p => p)}(x));
    F: Z{}
  }
$$ bend % --show
main = \{T: (x => \{Z: S{Z{}}; S: (p => p)}(x)); F: Z{}}
