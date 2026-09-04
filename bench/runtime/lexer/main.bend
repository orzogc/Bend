import Base
# Lexer: a tokenizer over generated source text, the suite's String
# stress case. Bend's String is a cons list, one node per character,
# so the lexer walks a linked list where C walks bytes; that gap is
# the point, and the program is spelled the natural way anyway.
# 2^size lines fork as a balanced batch tree. Leaf i hashes its index
# into a seed and expands the template
# "i = ( n o i ) o ( n o i ) o ( n o i ) ;" into one line of source:
# i becomes an identifier of 1-8 random lowercase letters, n a number
# of 1-6 random decimal digits, o one of + - * /, and any other
# template character copies itself; placeholder k draws from an
# xorshift stream salted by the seed and k, so the tail of the line
# is built first and each expansion is consed in front of it. The
# lexer then walks the line character by character as a three-mode
# machine (between tokens, inside an identifier, inside a number) and
# folds every token into the line checksum in order, acc = acc *
# 2654435761 ^ (kind * 40503 + payload): an identifier is kind 1 with
# the FNV-1a hash of its letters, a number kind 2 with its decimal
# value (wrapping), an operator or punctuation character kind 3 with
# its code; spaces are skipped. Line checksums sum up the fork tree.
# A template or source character is classified by comparisons on its
# code (there is no match on a word); a helper decides on the class.
#
# Sizes: small size = 8n (expect 1822208108), big size = 23n (expect
# 2401049475); both verified against the C twin.

type Slot is Data:
  Id{}
  Nm{}
  Op{}
  Lit{}

type Cls is Data:
  Letter{}
  Digit{}
  Space{}
  Punct{}

type Mode is Data:
  Gap{}
  InId{h: U32}
  InNm{v: U32}

# xorshift: x ^= x<<13; x ^= x>>17; x ^= x<<5
law prng:
  for +x: U32
  U32

def prng(x):
  +b = U32.xor(x, U32.shln(x, 13n))
  +d = U32.xor(b, U32.shrn(b, 17n))
  U32.xor(d, U32.shln(d, 5n))

# line seed: hash of the line index
law seed:
  for i: U32
  U32

def seed(i):
  prng(((i + 1) * 2654435761 : U32))

# placeholder seed: the line seed salted by the template position
law salt:
  for s: U32
  for k: U32
  U32

def salt(s, k):
  prng(U32.xor(s, (k * 2654435761 : U32)))

# the operator: + - * / by the two low bits of the seed
law op.pick:
  for b1: Bool
  for b0: Bool
  Char

def op.pick(b1, b0):
  match b1 b0:
    case False{} False{}:
      '+'
    case False{} True{}:
      '-'
    case True{} False{}:
      '*'
    case True{} True{}:
      '/'

law op:
  for +t: U32
  for rest: String
  String

def op(t, rest):
  SCon{op.pick(U32.is_ne(U32.and(t, 2), 0), U32.is_ne(U32.and(t, 1), 0)), rest}

# an identifier: n random lowercase letters, one prng step each
law ident:
  for n: Nat
  for t: U32
  for rest: String
  String

def ident(n, t, rest):
  match n:
    case 0n:
      rest
    case 1n+p:
      +u = prng(t)
      SCon{Chr{(97 + u % 26 : U32)}, ident(p, u, rest)}

# a number: n random decimal digits, one prng step each
law num:
  for n: Nat
  for t: U32
  for rest: String
  String

def num(n, t, rest):
  match n:
    case 0n:
      rest
    case 1n+p:
      +u = prng(t)
      SCon{Chr{(48 + u % 10 : U32)}, num(p, u, rest)}

# one placeholder in front of the rest of the line: an identifier of
# 1 + (t & 7) letters, a number of 1 + t % 6 digits, an operator, or
# the template character itself
law expand:
  for sl: Slot
  for c: U32
  for +t: U32
  for rest: String
  String

def expand(sl, c, t, rest):
  match sl:
    case Id{}:
      ident(U32.to_nat((1 + U32.and(t, 7) : U32)), t, rest)
    case Nm{}:
      num(U32.to_nat((1 + t % 6 : U32)), t, rest)
    case Op{}:
      op(t, rest)
    case Lit{}:
      SCon{Chr{c}, rest}

# the slot of a template character: i, n, o, or a literal
law slot.go:
  for i: Bool
  for n: Bool
  for o: Bool
  Slot

def slot.go(i, n, o):
  match i n o:
    case True{} _ _:
      Id{}
    case _ True{} _:
      Nm{}
    case _ _ True{}:
      Op{}
    case _ _ _:
      Lit{}

law slot:
  for +c: U32
  Slot

def slot(c):
  slot.go(U32.is_eq(c, 105), U32.is_eq(c, 110), U32.is_eq(c, 111))

# one template character, read twice: for its slot and as a literal
law gen.at:
  for +c: U32
  for t: U32
  for rest: String
  String

def gen.at(c, t, rest):
  expand(slot(c), c, t, rest)

# the line: the template expanded character by character, placeholder
# k seeded by salt(s, k), each expansion consed onto the built tail
law gen:
  for tpl: String
  for +s: U32
  for +k: U32
  String

def gen(tpl, s, k):
  match tpl:
    case SNil{}:
      SNil{}
    case SCon{Chr{c}, u}:
      gen.at(c, salt(s, k), gen(u, s, (k + 1 : U32)))

law tpl:
  String

def tpl():
  "i = ( n o i ) o ( n o i ) o ( n o i ) ;"

# the class of a source character
law cls.go:
  for l: Bool
  for d: Bool
  for s: Bool
  Cls

def cls.go(l, d, s):
  match l d s:
    case True{} _ _:
      Letter{}
    case _ True{} _:
      Digit{}
    case _ _ True{}:
      Space{}
    case _ _ _:
      Punct{}

law cls:
  for +c: U32
  Cls

def cls(c):
  cls.go(U32.is_le(97, c) && U32.is_le(c, 122),
    U32.is_le(48, c) && U32.is_le(c, 57), U32.is_eq(c, 32))

# one token into the line checksum
law mix:
  for acc: U32
  for kind: U32
  for x: U32
  U32

def mix(acc, kind, x):
  U32.xor((acc * 2654435761 : U32), (kind * 40503 + x : U32))

# FNV-1a: one letter into the identifier hash
law fnv:
  for h: U32
  for c: U32
  U32

def fnv(h, c):
  (U32.xor(h, c) * 16777619 : U32)

# the machine: (mode, acc) steps over one classified character; a
# letter extends an identifier, a digit a number, and anything else
# closes the open token, then starts what the character begins
law step.at:
  for m: Mode
  for k: Cls
  for c: U32
  for acc: U32
  Mode & U32

def step.at(m, k, c, acc):
  match m k:
    case Gap{} Letter{}:
      (InId{fnv(2166136261, c)}, acc)
    case Gap{} Digit{}:
      (InNm{(c - 48 : U32)}, acc)
    case Gap{} Space{}:
      (Gap{}, acc)
    case Gap{} Punct{}:
      (Gap{}, mix(acc, 3, c))
    case InId{h} Letter{}:
      (InId{fnv(h, c)}, acc)
    case InId{h} Digit{}:
      (InNm{(c - 48 : U32)}, mix(acc, 1, h))
    case InId{h} Space{}:
      (Gap{}, mix(acc, 1, h))
    case InId{h} Punct{}:
      (Gap{}, mix(mix(acc, 1, h), 3, c))
    case InNm{v} Letter{}:
      (InId{fnv(2166136261, c)}, mix(acc, 2, v))
    case InNm{v} Digit{}:
      (InNm{(v * 10 + (c - 48) : U32)}, acc)
    case InNm{v} Space{}:
      (Gap{}, mix(acc, 2, v))
    case InNm{v} Punct{}:
      (Gap{}, mix(mix(acc, 2, v), 3, c))

law step:
  for m: Mode
  for +c: U32
  for acc: U32
  Mode & U32

def step(m, c, acc):
  step.at(m, cls(c), c, acc)

# end of line: close the open token
law flush:
  for m: Mode
  for acc: U32
  U32

def flush(m, acc):
  match m:
    case Gap{}:
      acc
    case InId{h}:
      mix(acc, 1, h)
    case InNm{v}:
      mix(acc, 2, v)

# the lexer: one step per character, (mode, acc) riding as r
law lex:
  for s: String
  for r: Mode & U32
  U32

def lex(s, r):
  match s:
    case SNil{}:
      (m, acc) = r
      flush(m, acc)
    case SCon{Chr{c}, t}:
      (m, acc) = r
      lex(t, step(m, c, acc))

# one line: generate it, then lex it
law line:
  for i: U32
  U32

def line(i):
  lex(gen(tpl(), seed(i), 0), (Gap{}, 0))

# batch tree over the line index space; line checksums sum
law batch:
  for +d: Nat
  for +i: U32
  U32

def batch(d, i):
  match d:
    case 0n:
      line(i)
    case 1n+p:
      a b = batch(p, i) batch(p, (i + U32.shln(1, p) : U32))
      (a + b : U32)

law size.small:
  Nat

def size.small():
  8n

law expect.small:
  U32

def expect.small():
  1822208108

law size.big:
  Nat

def size.big():
  23n

law expect.big:
  U32

def expect.big():
  2401049475

law main:
  IO(Unit)

def main():
  IO.print(U32.show(batch!(size.big(), 0)))
