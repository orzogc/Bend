# a constructor spells its continuation as a trailing lambda, and the
# residual effect tree prints back through the printer
# ported from bend3: local IO renamed (base owns the name), words become
# ctor nats, the doubled x + t goes affine
type W:
  Z{}
  S{p: W}

type Io:
  Done{value: W}
  Tick{cont: W -> Io}
  Print{text: W, cont: W -> Io}

assert go:
  forall f: W -> Io
  Io

def go(f):
  f(S{Z{}})

assert main:
  Io

def main():
  go(n => Print{n, x => Tick{t => Done{S{x}}}})
$$ bend % --show
go = f => f(S{Z{}})
main = go(n => Print{n, x => Tick{t => Done{S{x}}}})
