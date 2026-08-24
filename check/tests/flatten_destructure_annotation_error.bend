# a destructure's value annotation applies: a wrong annotation is a
# type error, not a no-op.
# ported from bend3: `P = e : T` spells the Ann brace, P = {e : T}
import Base

type Pw2:
  Pq2{a: U32, b: U32}

type Bw7:
  Tw7{}

assert swap:
  forall p: Pw2
  Pw2

def swap(p):
  Pq2{x, y} = {p : Bw7}
  Pq2{y, x}

assert main:
  Pw2

def main(): swap(Pq2{1, 2})
$$ bend %
Error:
- expected : Bw7
- observed : Pw2
Context:
- p : Pw2
Location: swap