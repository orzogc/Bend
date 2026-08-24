# bend3's fork cap ACCEPTED its widest legal 32-sibling parallel let;
# bend4's typed fork-let pairs right-nested with no cap at all (the
# dead-cap law carried, parse_fork_arity_cap_000), so the same 32
# siblings join into one sum on every lane: sum(2i+1, i<32) = 1024
import Base

assert leaf:
  forall i: U32
  U32

def leaf(i):
  (i * 2) + 1

assert burst:
  U32

def burst():
  & x0 : U32 = leaf(0) & x1 : U32 = leaf(1) & x2 : U32 = leaf(2) & x3 : U32 = leaf(3) & x4 : U32 = leaf(4) & x5 : U32 = leaf(5) & x6 : U32 = leaf(6) & x7 : U32 = leaf(7) & x8 : U32 = leaf(8) & x9 : U32 = leaf(9) & x10 : U32 = leaf(10) & x11 : U32 = leaf(11) & x12 : U32 = leaf(12) & x13 : U32 = leaf(13) & x14 : U32 = leaf(14) & x15 : U32 = leaf(15) & x16 : U32 = leaf(16) & x17 : U32 = leaf(17) & x18 : U32 = leaf(18) & x19 : U32 = leaf(19) & x20 : U32 = leaf(20) & x21 : U32 = leaf(21) & x22 : U32 = leaf(22) & x23 : U32 = leaf(23) & x24 : U32 = leaf(24) & x25 : U32 = leaf(25) & x26 : U32 = leaf(26) & x27 : U32 = leaf(27) & x28 : U32 = leaf(28) & x29 : U32 = leaf(29) & x30 : U32 = leaf(30) & x31 : U32 = leaf(31);
  ((((((((((((((((((((((((((((((x0 + x1) + x2) + x3) + x4) + x5) + x6) + x7) + x8) + x9) + x10) + x11) + x12) + x13) + x14) + x15) + x16) + x17) + x18) + x19) + x20) + x21) + x22) + x23) + x24) + x25) + x26) + x27) + x28) + x29) + x30) + x31

assert main.out:
  Nat

def main.out():
  U32.to_nat(burst())

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
1024n
$$ bend % --seq
1024n
exit 0
$$ bend % --par
1024n
exit 0
$$ bend % --js
1024n
exit 0
