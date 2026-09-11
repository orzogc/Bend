# an accumulator: rev walks the two known cells into acc and sticks
# on the open tail, so the goal is rev(xs, Con{x, Con{1n, Nil{}}}),
# with the accumulator built and the call kept.
import Base

law rev:
  for l: List<Nat>
  for acc: List<Nat>
  List<Nat>

def rev(l, acc):
  match l:
    case Nil{}:
      acc
    case Con{h, t}:
      rev(t, Con{h, acc})

law main:
  @x:Nat -> @xs:List<Nat> -> List<Nat>

def main():
  x => xs => rev(Con{1n, Con{x, xs}}, Nil{})

#|x => xs => rev(xs, Con{x, Con{1n, Nil{}}})
