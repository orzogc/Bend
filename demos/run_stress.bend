#[halts]
#
# `#[halts]` heads the file: it licenses live calls into the bodiless
# asserts below (the runtime's native surface) and spawn's forks, whose
# split-off depths are not syntactic subterms.
#
# Self-contained: the file declares every type it touches and asserts
# the native ops it needs. Each assert is named after its runtime.js
# intrinsic (U32.add is u32_add, ...), so the JS backend wires the
# compiled program straight to the real natives. Sharing is spelled with
# cloned (+) binders; the C runtime backs each with its RC redirector.
# The evaluator has no natives, so churn's per-char branch on Rt.eqz
# stays stuck and main's normal form is the tree of every
# native-decision path: ~2x per seed char, terabytes at 30 chars.
# Checking passes; run it through a real backend, which decides each
# branch.
#
# One algorithm, three defs. `spawn` builds a depth-20 tree of array
# transformers by fork/join: each of the 1,048,576 leaves is a heap
# closure capturing four U32s, each of the 1,048,575 nodes a
# composition closure capturing its two child closures, so closures are
# stored inside envs and extracted again at application; the two
# recursive calls per node are independent (the parallelism), and each
# node also sums its forks' values (a parallel reduction). The tree
# escapes to main as one affine value holding 2,097,151 environments.
# main applies the root once to a fresh 64-slot array: every leaf then
# fires a read-modify-write THROUGH its captured env (~4M native ops),
# and each spent environment feeds the collector. `churn` drains the
# result: per seed character, one native swap at a slot chosen by the
# accumulator, one digit char emitted from what the slot held, one Bool
# branch on that digit, tail call; at SNil the accumulator and the
# whole live array drop (collector again). The output depends on both
# the parallel sum (it seeds the walk) and the array contents (read
# back per char), so any wrong op anywhere changes the printed string.
#
# Literals stress the intros: the seed string and both chars expand to
# full SCon/Chr/U32/Word trees at the checker, 20n/6n to Succ chains;
# at runtime they are native strings, chars and nats. churn compiles to
# a while(true) loop; spawn compiles to a real fork.

# Base types (the literal/sugar surface this file touches)
# --------------------------------------------------------

type Bool:
  False{}
  True{}

type Nat:
  Zero{}
  Succ{pred: Nat}

type Sigma<-A: Type, -B: @-x: A -> Type>:
  Tuple{fst: A, snd: B(fst)}

def Pair(-A: Type, -B: Type) -> Type:
  Sigma<A, _ => B>

assert Word:
  forall n: Nat
  Type

type Word.Nil:
  WNil{}

type Word.Con<-p: Nat>:
  WCon{head: Bool, tail: Word(p)}

def Word(n):
  match n:
    case 0n:
      Word.Nil
    case 1n+p:
      Word.Con<p>

type U32:
  U32{data: Word(32n)}

type Char:
  Chr{code: U32}

type String:
  SNil{}
  SCon{head: Char, tail: String}

type Array<T: Type>:
  ALeaf{value: T}
  ANode{xs: Array<T>, ys: Array<T>}

# The native surface: bodiless asserts, one per runtime.js intrinsic
# ------------------------------------------------------------------

assert U32.add:
  forall a: U32
  forall b: U32
  U32

assert U32.mul:
  forall a: U32
  forall b: U32
  U32

assert U32.div:
  forall a: U32
  forall b: U32
  U32

assert U32.mod:
  forall a: U32
  forall b: U32
  U32

assert U32.is_zero:
  forall a: U32
  Bool

assert Array.swap:
  forall a: Array<U32>
  forall i: U32
  forall v: U32
  Array<U32> & U32

# Rt: the mocked C runtime's surface, adapted over the natives
# ------------------------------------------------------------

def Rt.add(a: U32, b: U32) -> U32:
  U32.add(a, b)

def Rt.mul(a: U32, b: U32) -> U32:
  U32.mul(a, b)

def Rt.divmod(+a: U32, +b: U32) -> U32 & U32:
  (U32.div(a, b), U32.mod(a, b))

def Rt.eqz(a: U32) -> Bool:
  U32.is_zero(a)

def Rt.alloc(+n: Nat, +x: U32) -> Array<U32>:
  match n:
    case 0n:
      ALeaf{x}
    case 1n+p:
      ANode{Rt.alloc(p, x), Rt.alloc(p, x)}

# read slot i without net effect: swap i in (reading the old value),
# then swap the old value back; the value crosses the seam twice
def Rt.read(b: Array<U32>, +i: U32) -> Array<U32> & U32:
  (b2, v) = Array.swap(b, i, i)
  +w = {v : U32}
  (b3, z) = Array.swap(b2, i, w)
  (b3, w)

def Rt.write(b: Array<U32>, i: U32, v: U32) -> Array<U32>:
  (b2, old) = Array.swap(b, i, v)
  b2

def Rt.swap(b: Array<U32>, i: U32, v: U32) -> Array<U32> & U32:
  Array.swap(b, i, v)

# Parallel closure tree: 2^d leaf transformers, 2^d - 1 compositions.
# A leaf captures {i, s, q} and, only when applied, reads slot
# s mod 48, mixes the read value with its captures, and writes it back:
# an array read-modify-write through a closure environment. A node
# captures its two child closures and composes them; its two forks are
# independent and their values join by add. Left seed s+m, right s*s,
# so every path gets a distinct polynomial of the root seed.
def spawn(+d: Nat, +m: U32, +s: U32) -> U32 & (Array<U32> -> Array<U32>):
  match d:
    case 0n:
      (q, i) = Rt.divmod(s, m)
      +j = {i : U32}
      (s, b => \{Tuple: b2 => old =>
        Rt.write(b2, j, Rt.add(Rt.mul(old, s), q))}(Rt.read(b, j)))
    case 1n+p:
      (va, fa) = spawn(p, m, Rt.add(s, m))
      (vb, fb) = spawn(p, m, Rt.mul(s, s))
      (Rt.add(va, vb), b => fb(fa(b)))

# String-driven drain: per character, one native swap at slot acc mod
# 48 (z is 48 < 64 slots), one digit char from what the slot held
# (t is 10, z doubles as the '0' offset), one Bool branch on that
# digit steering the next mix, tail call. h drops in the branch that
# skips it (affine); at SNil acc and the whole live array drop.
def churn(s: String, +t: U32, +z: U32, b: Array<U32>, acc: U32, out: String) -> String:
  match s:
    case SNil{}:
      out
    case SCon{Chr{c}, cs}:
      (q, i)    = Rt.divmod(acc, z)
      (b2, old) = Rt.swap(b, i, q)
      +o = {old : U32}
      (h, r)    = Rt.divmod(o, t)
      +u = {r : U32}
      match Rt.eqz(u):
        case True{}:
          churn(cs, t, z, b2, Rt.add(o, c), SCon{Chr{Rt.add(z, u)}, out})
        case False{}:
          churn(cs, t, z, b2, Rt.add(Rt.mul(o, c), h), SCon{Chr{Rt.add(z, u)}, out})

# The match extracts numeric constants: a char literal is the only U32
# literal in source, and Chr must be matched to reach the code. '\n' is
# 10 (the digit base and the tree seed); '0' is 48 (the digit offset,
# the alloc fill, and the slot modulus: 48 < 64 = 2^6n slots, so every
# index is in range). f(...) fires the million leaf envs; v, their
# parallel sum, seeds the drain.
def main() -> String:
  match {'\n' : Char} {'0' : Char}:
    case Chr{t} Chr{z}:
      +a = {t : U32}
      +c = {z : U32}
      (v, f) = spawn(20n, c, a)
      churn("Bend stresses its own runtime!", a, c, f(Rt.alloc(6n, c)), v, "")
