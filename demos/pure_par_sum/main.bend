# Parallel sum: the smallest fork/join program. tree(d, i) adds the 2^d
# numbers i .. i + 2^d - 1 as a balanced tree: a leaf (d = 0) is its
# number; a node forks two halves with the parallel let `a b = f g`,
# waits for both and adds them. The tree is a template over the number
# type, its addition and the jump to the right half's start, so one
# body serves two instances: sum, at U32, is what main runs; sum_nat,
# at Nat, is what LAWS.bend proves equal to the sequential loop seq.
# main calls sum!(16n, 0): the `!` sends the call to the GPU when the
# machine has one, else to every CPU core; interpreted, the same tree
# runs sequentially.
#
# Run:
#   bend demos/pure_par_sum/main.bend                    (interprets)
#   bend demos/pure_par_sum/main.bend -o sum && ./sum    (the GPU, or every core)
#   ./sum --gpu off                                      (every core)
#   ./sum --gpu off --threads 1                          (one core)
#
# main sums 0 .. 65535, which is 65535 * 65536 / 2 = 2147450880.
import Base

# tree
# ----
# the leaves i .. i + 2^d - 1 as a balanced fork/join tree: the left
# half starts at i, the right half at jump(p, i), 2^p numbers later
def tree(~A: Data, ~plus: A -> A -> A, ~jump: Nat -> A -> A, +d: Nat, +i: A) -> A:
  match d:
    case 0n:
      i
    case 1n++p:
      a b = tree(~A, ~plus, ~jump, p, i) tree(~A, ~plus, ~jump, p, jump(p, i))
      plus(a, b)

# at U32: the right half starts at i + 2^p
def sum(+d: Nat, +i: U32) -> U32:
  tree(~U32, ~U32.add, ~(p => i => (i + U32.shln(1, p) : U32)), d, i)

# Spec
# ----
# the same tree at Nat, and the sequential loop it must equal:
# seq(n, i) adds i, i + 1, .., i + n - 1 one by one

def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n+p:
      1n+add(p, b)

def pow2(d: Nat) -> Nat:
  match d:
    case 0n:
      1n
    case 1n+p:
      +h = pow2(p)
      add(h, h)

def jump(p: Nat, i: Nat) -> Nat:
  add(pow2(p), i)

def sum_nat(+d: Nat, +i: Nat) -> Nat:
  tree(~Nat, ~add, ~jump, d, i)

def seq(n: Nat, +i: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+m:
      add(i, seq(m, 1n+i))

def main() -> U32:
  sum!(16n, 0)
