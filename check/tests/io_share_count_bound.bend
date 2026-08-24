# io (io_share_count_bound): the redirect count saturates LOUD. A
# redirect is ONE word - a 40-bit target above a 24-bit count - so a
# term kept past RFC_CNT has nowhere to count: rfc_bump posts error
# 9 the moment the count nears the field's edge, never lets it carry
# into the target bits. NOTHING drove it: gutting the guard kept the
# whole suite green (989/989) while this program answered a CORRUPT
# string and exit 0 - the wrapped count overflowed into the target
# address, the alias resolved to a poisoned node, silent wrong
# output. The drive is honest: one +String binder kept once per
# level of a 17M-step tail loop, every alias held live in the
# accumulated list, one redirect cell climbing to the edge. The JS
# lanes are the wide side and stay honest, RECORDED: the host GC
# owns memory and no count exists, so the same program prints "x"
# and exits 0 - the C refusal is a capacity law of the one-word
# redirect, the io_stack_fault_trap class with the lanes reversed.
# The undrivable arm of the same law - a shared closure or task
# refuses at rfc_wrap (the compiler defines CLO_SHR and seals
# environments before any closure is ever kept, so no honest program
# reaches it) - rides on csrc pins holding both guard sites.
# csrc has: if ((c & RFC_CNT) >= RFC_CNT - 1) {
# csrc has: if (term_tag(t) == TAG_CLO || term_tag(t) == TAG_TSK) {
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

assert hold:
  forall n: Nat
  forall +s: (+ String ~ Str.copy)
  forall acc: List<String>
  List<String>

def hold(n, s, acc):
  match n:
    case 0n:
      Con{s, acc}
    case 1n+p:
      hold(p, s, Con{s, acc})

assert first:
  forall l: List<String>
  String

def first(l):
  match l:
    case Nil{}:
      "empty"
    case Con{h, t}:
      h

assert main:
  IO(U32)

def main():
  do IO<U32>:
    u : Unit <- IO.print(first(hold(U32.to_nat(17000000), "x", Nil{})))
    return 0
$$ bend %
x
$$ bend % --js
x
exit 0
$$ bend % --seq
bend: error 9: runtime fail-stop
signal SIGABRT
$$ bend % --par
bend: error 9: runtime fail-stop
signal SIGABRT
