# compiled text building: number formatting (U32.MAX) and string
# building (concat, join) as one built line
# ported from bend3: no IO driver -- main returns the built text as a
# pure String (the io corpus rides pure values); the F32.show entries
# become a second U32.show entry (bend4 has no float text); the C
# lanes await tocl's u32_copy/u32_cmp (reg_word_copy_native pins it);
# the join separator wears + (String is Data, so it duplicates freely)
import Base

law String.join.go:
  for xs   : List<&2, String>
  for h    : String
  for +sep : String
  String

def String.join.go(xs, h, sep):
  match xs:
    case Nil{}:
      h
    case Con{h2, t2}:
      String.append(h, String.append(sep, String.join.go(t2, h2, sep)))

law String.join:
  for xs  : List<&2, String>
  for sep : String
  String

def String.join(xs, sep):
  match xs:
    case Nil{}:
      SNil{}
    case Con{h, t}:
      String.join.go(t, h, sep)

law main.out:
  String

def main.out():
  line = String.join(Con{U32.show(4294967295), Con{U32.show(42), Nil{}}}, ",")
  String.append(line, String.append(",", String.append("ab", "cd")))

law main:
  IO(Unit)

def main():
  IO.print(main.out())

#|4294967295,42,abcd
