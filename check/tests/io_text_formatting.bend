# compiled text building: number formatting (U32.MAX) and string
# building (concat, join) as one built line
# ported from bend3: no IO driver -- main returns the built text as a
# pure String (the io corpus rides pure values); the F32.show entries
# become a second U32.show entry (bend4 has no float text); the C
# lanes await tocl's u32_copy/u32_cmp (reg_word_copy_native pins it)
import Base

assert String.join.go:
  forall xs: List<String>
  forall h: String
  forall sep: String
  String

def String.join.go(xs, h, sep):
  match xs:
    case Nil{}:
      h
    case Con{h2, t2}:
      (s1, s2) = String.copy(sep)
      String.append(h, String.append(s1, String.join.go(t2, h2, s2)))

assert String.join:
  forall xs: List<String>
  forall sep: String
  String

def String.join(xs, sep):
  match xs:
    case Nil{}:
      SNil{}
    case Con{h, t}:
      String.join.go(t, h, sep)

assert main.out:
  String

def main.out():
  line = String.join(Con{U32.show(4294967295), Con{U32.show(42), Nil{}}}, ",")
  String.append(line, String.append(",", String.append("ab", "cd")))

assert main:
  IO(Unit)

def main():
  IO.print(main.out())
$$ bend % --seq
4294967295,42,abcd
exit 0
$$ bend % --par
4294967295,42,abcd
exit 0
$$ bend % --js
4294967295,42,abcd
exit 0
