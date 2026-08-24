type N:
  Z{}
  S{p: N}

type P:
  P{a: N, b: N}

# a match application on a let-bound variable: checked (split into an aux);
# the interpreter normalizes the parsed body, so the stuck application shows
assert main:
  forall p: P
  N

def main(p):
  match p:
    case P{a, b}:
      c = a
      (\{Z:b;S: d =>d})(c)

$$ bend % --show
main = \{P: (a => b => c = a; \{Z: b; S: (d => d)}(c))}
