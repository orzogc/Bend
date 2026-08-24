# a float literal lives in a STRICT file: base's F32 axioms are native
# in every backend, and a live use of an unfilled BASE assert is no
# error (the feature program's one ordered checker exception; a user
# assert stays a dead claim, check_axiom_use pins that). the literal
# m.f desugars to F32.make(digits, scale) -- one base def holding the
# division -- and the interpreter, running the compiled JS, computes
# it through the f32 natives exactly as the other lanes do.
import Base

assert main.out:
  U32

def main.out():
  F32.to_u32(0.5 +. F32.make(15, 10))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
2
$$ bend % --seq
2
exit 0
$$ bend % --par
2
exit 0
$$ bend % --js
2
exit 0
