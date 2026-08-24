# io (io_rfc_saturation): redirect count saturation is LOUD - the
# one numbered line, never a wrapped count. A redirect is one word,
# target<<24 | count, so the count is 24 bits: the 16777214th live
# alias of one term must die "bend: error 9", because one more bump
# carries into the target bits. NOTHING drove it: gutting rfc_bump's
# guard kept the whole suite green while this program wrapped its
# count, saw a false "last owner" on a mid-walk drop, double-freed
# the shared node and printed a clean answer - the silent-loss class
# the numbered-error law forbids, here with no symptom at all. The
# drive is honest: +s over the Str.copy witness is kept once per
# iteration and every alias is held live in a List, so the count is
# the list's length; 16777300 iterations saturate in under a quarter
# second in both C lanes. The js and interp lanes ride the host GC,
# where no count exists: they run the same program whole and print
# the honest length, proving the program is not a crash oracle; the
# 24-bit count is the machine's recorded representation bound. The
# other RFCS halves ride on no honest program (a book that shares
# closures compiles with CLO_SHR; carbonized tasks stay linear; a
# hot book's seam values arrive sealed), so csrc pins hold the
# share-refusal sites, span_fade's raw-field post, the saturation
# guard and the count width verbatim.
# csrc has: #define RFC_CNT  ((1u << 24) - 1)
# csrc has: if ((c & RFC_CNT) >= RFC_CNT - 1) {
# csrc has: if (term_tag(t) == TAG_CLO || term_tag(t) == TAG_TSK) {
# csrc has: if (term_tag(t) == TAG_TSK) {
# csrc has: } else if (!term_triv(f)) {
import Base

assert Chr.copy:
  forall c: Char
  Copy(Char, c) & Copy(Char, c)

def Chr.copy(c):
  match c:
    case Chr{n}:
      ((nx, ne), (ny, nf)) = U32.copy(n)
      e1 = Equal.cong(U32, Char, z => Chr{z}, n, nx, ne)
      e2 = Equal.cong(U32, Char, z => Chr{z}, n, ny, nf)
      ((Chr{nx}, e1), (Chr{ny}, e2))

assert Str.copy:
  forall s: String
  Copy(String, s) & Copy(String, s)

def Str.copy(s):
  match s:
    case SNil{}:
      ((SNil{}, {==}), (SNil{}, {==}))
    case SCon{h, t}:
      ((hx, he), (hy, hf)) = Chr.copy(h)
      ((tx, te), (ty, tf)) = Str.copy(t)
      s10 = Equal.cong(Char, String, z => SCon{z, t}, h, hx, he)
      s11 = Equal.cong(String, String, z => SCon{hx, z}, t, tx, te)
      t11 = Equal.trans(String, SCon{h, t}, SCon{hx, t}, SCon{hx, tx}, s10, s11)
      s20 = Equal.cong(Char, String, z => SCon{z, t}, h, hy, hf)
      s21 = Equal.cong(String, String, z => SCon{hy, z}, t, ty, tf)
      t21 = Equal.trans(String, SCon{h, t}, SCon{hy, t}, SCon{hy, ty}, s20, s21)
      ((SCon{hx, tx}, t11), (SCon{hy, ty}, t21))

assert spin:
  forall m: Nat
  forall +s: (+ String ~ Str.copy)
  forall acc: List<String>
  List<String>

def spin(m, s, acc):
  match m:
    case 0n:
      Con{s, acc}
    case 1n+p:
      spin(p, s, Con{s, acc})

assert count:
  forall xs: List<String>
  forall k: U32
  U32

def count(xs, k):
  match xs:
    case Nil{}:
      k
    case Con{h, t}:
      count(t, k + 1)

assert run:
  forall n: U32
  U32

def run(n):
  count(spin(U32.to_nat(n), U32.show(41), Nil{}), 0)

assert main:
  IO(U32)

def main():
  do IO<U32>:
    u : Unit <- IO.print(U32.show(run(16777300)))
    return 0
$$ bend %
16777301
$$ bend % --seq
bend: error 9: runtime fail-stop
signal SIGABRT
$$ bend % --par
bend: error 9: runtime fail-stop
signal SIGABRT
$$ bend % --js
16777301
exit 0
