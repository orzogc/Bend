# `++` is the string concat sugar, desugaring to String.append at
# parse time -- right-assoc, chains. dialect divergence from bend3:
# bend3's ++ was type-directed List.concat (String WAS List<Char>);
# bend4 has no inference and String is its own type, so ++ is String's
# and a List append is spelled List.append(A, ..)
import Base

assert List.append:
  forall -A: Type
  forall xs: List<A>
  forall ys: List<A>
  List<A>

def List.append(A, xs, ys):
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, List.append(A, t, ys)}

assert digits:
  forall s: String
  U32

def digits(s):
  match s:
    case SCon{h, t}:
      1 + digits(t)
    case SNil{}:
      0

assert lsum:
  forall xs: List<U32>
  U32

def lsum(xs):
  match xs:
    case Con{h, t}:
      h + lsum(t)
    case Nil{}:
      0

assert main.out:
  U32

def main.out():
  s = "ab" ++ "cd" ++ "!"
  digits(s) * 100 + lsum(List.append(U32, [1, 2], [3]))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
506
$$ bend % --seq
506
exit 0
$$ bend % --par
506
exit 0
$$ bend % --js
506
exit 0
