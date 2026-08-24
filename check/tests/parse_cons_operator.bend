# cons operator h<>t, in terms and patterns -- ported from bend3.
# dialect divergence: bend4's String is its own SCon/SNil type, not
# List<Char>, so <> builds List's Con only; lc respells a String as
# List<Char> with both sugars, and the '/'-pair test rides Char.eq
# over cons PATTERNS (a char-literal pattern is a 32-ctor word tree,
# not a pattern; Char.eq rides U32.cmp, the reg_word_copy_native
# tocl seam, so the codes compare as U32 -- '/' is 47)
import Base

assert lc:
  forall s: String
  List<Char>

def lc(s):
  match s:
    case SCon{h, t}:
      h <> lc(t)
    case SNil{}:
      []

assert len:
  forall s: List<Char>
  U32

def len(s):
  match s:
    case Con{h, t}:
      1 + len(t)
    case Nil{}:
      0

assert slashes:
  forall s: List<Char>
  U32

def slashes(s):
  match s:
    case Chr{a} <> Chr{b} <> t:
      if U32.is_eq(a, 47) && U32.is_eq(b, 47): 1 else: 0
    case t:
      0

assert main.out:
  U32

def main.out():
  len('a' <> lc("bc")) * 100 + 65 + (122 - 97) + slashes(lc("//x")) + slashes(lc("/x")) * 10

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
391
$$ bend % --seq
391
exit 0
$$ bend % --par
391
exit 0
$$ bend % --js
391
exit 0
