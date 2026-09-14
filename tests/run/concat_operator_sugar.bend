# `++` is the string concat sugar, desugaring to String.append at
# parse time -- right-assoc, chains. dialect divergence from bend3:
# bend3's ++ was type-directed List.concat (String WAS List<Char>);
# and a List append is spelled List.append(a, A, ..)
import Base

law List.append:
  for -a : Quant
  for -A : Kind(a)
  for xs : List<a, A>
  for ys : List<a, A>
  List<a, A>

def List.append(a, A, xs, ys):
  match xs:
    case Nil{}:
      ys
    case h <> t:
      h <> List.append(a, A, t, ys)

law digits:
  for s: String
  U32

def digits(s):
  match s:
    case SCon{h, t}:
      (1 + digits(t) : U32)
    case SNil{}:
      0

law lsum:
  for xs: List<&2, U32>
  U32

def lsum(xs):
  match xs:
    case h <> t:
      (h + lsum(t) : U32)
    case Nil{}:
      0

law main.out:
  U32

def main.out():
  s = "ab" ++ "cd" ++ "!"
  (digits(s) * 100 + lsum(List.append(&2, U32, [1, 2], [3])) : U32)

law main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))

#|506
