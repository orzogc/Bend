# refusal pin: bend3's file redefined Pair.Pair to elaborate a raw
# tuple field into a function type, and its own golden was the
# duplicate-declaration refusal -- the negative-self-application Empty
# never checked. bend4 hits the same first wall: a Base name cannot be
# redeclared (and bend4 has no Data table for the redefinition to
# poison; the D/delta skeleton below the dying line is inert).
# ported from bend3: Pair.Pair -> String.eq (bend4's base owns no
# Pair; the wall is the name, not the signature)
import Base

assert String.eq:
  forall a: String
  forall b: String
  Bool

def String.eq(a, b):
  True{}

type D2<result: Type>:
  MkD2{fun: D2<result> -> result}

assert delta:
  forall -answer: Type
  forall value: D2<answer>
  answer

def delta(answer, value):
  delta.go(value, value)

assert delta.go:
  forall -answer: Type
  forall saved: D2<answer>
  forall value: D2<answer>
  answer

def delta.go(answer, saved, value):
  match value:
    case MkD2{step}:
      step(saved)

assert main:
  Empty

def main(): delta(Empty, MkD2{delta(Empty)})
$$ bend %
Error:
- expected : a fresh name (duplicate declaration: String.eq)
- observed : ':'
Location:
10 | 
11>| assert String.eq:
12 |   forall a: String
