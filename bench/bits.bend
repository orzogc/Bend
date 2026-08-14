import Base
# Bits: binary-counter busy walk over a 25-bit LSB-first list, ported
# from Bend3's seq_hvm_bits.bend. One step: dic (increment scan), rev,
# dac (busy scan), rev. Checksum: djb2-style fold of the final list in
# the source's term encoding, then mix with N. main checks the checksum
# against the known constant and returns Bool.
#
# Sizes: small N = 10 (expect 1298439335), big N = 138200000
# (expect 861627957, verified against Bend3).

type Bits:
  E{}
  O{pred: Bits}
  I{pred: Bits}

# u32 constant from base-2^10 digits: a*2^20 + b*2^10 + c
def u32d(a: Nat, b: Nat, c: Nat) -> U32:
  U32.add(U32.shln(20n, U32.from_nat(a)), U32.add(U32.shln(10n, U32.from_nat(b)), U32.from_nat(c)))

# 0001011111100010110100111, LSB-first (value 30099432)
def Bits.init() -> Bits:
  O{O{O{I{O{I{I{I{I{I{I{O{O{O{I{O{I{I{O{I{O{O{I{I{I{E{}}}}}}}}}}}}}}}}}}}}}}}}}}

# increment scan: trailing 1s flip to 0 onto acc; the first 0 flips to 1
def Bits.dic(bits: Bits, acc: Bits) -> Bits & Bits:
  match bits:
    case E{}:
      (acc, E{})
    case O{p}:
      (acc, I{p})
    case I{p}:
      Bits.dic(p, O{acc})

# fold a reversed prefix back onto the rest
def Bits.rev(acc: Bits, rest: Bits) -> Bits:
  match acc:
    case E{}:
      rest
    case O{p}:
      Bits.rev(p, O{rest})
    case I{p}:
      Bits.rev(p, I{rest})

# busy scan: walk leading 0s onto acc, stop at the first 1
def Bits.dac(bits: Bits, acc: Bits) -> Bits & Bits:
  match bits:
    case E{}:
      (acc, E{})
    case O{p}:
      Bits.dac(p, O{acc})
    case I{p}:
      (acc, I{p})

def Bits.step.dac(bits: Bits) -> Bits:
  (acc, rest) = Bits.dac(bits, E{})
  Bits.rev(acc, rest)

# one busy-walk step: increment, restore, scan, restore
def Bits.step(bits: Bits) -> Bits:
  (acc, rest) = Bits.dic(bits, E{})
  Bits.step.dac(Bits.rev(acc, rest))

def Bits.run(fuel: Nat, bits: Bits) -> Bits:
  match fuel:
    case 0n:
      bits
    case 1n+p:
      Bits.run(p, Bits.step(bits))

# h*33 + x
def Bits.mix(h: U32, x: U32) -> U32:
  match U32.copy(h):
    case ((h1, e1), (h2, e2)):
      U32.add(U32.add(U32.shln(5n, h1), h2), x)

# 2^24: the Pak/Won word of a 1-bit chain in the source's term encoding
def Bits.pak() -> U32:
  U32.shln(24n, U32.one())

# hash prefix of one list node: tags 13, 15, 14
def Bits.hash.cons(h: U32, b: U32) -> U32:
  h1 = Bits.mix(Bits.mix(h, U32.from_nat(13n)), Bits.pak())
  h2 = Bits.mix(h1, U32.from_nat(15n))
  Bits.mix(Bits.mix(h2, U32.from_nat(14n)), U32.add(Bits.pak(), b))

def Bits.hash(bits: Bits, h: U32) -> U32:
  match bits:
    case E{}:
      Bits.mix(Bits.mix(h, U32.from_nat(14n)), U32.inc(Bits.pak()))
    case O{p}:
      Bits.hash(p, Bits.hash.cons(h, U32.zero()))
    case I{p}:
      Bits.hash(p, Bits.hash.cons(h, U32.one()))

# 5381
def Bits.seed() -> U32:
  U32.from_nat(Nat.add(Nat.mul(5n, Nat.pow2(10n)), 261n))

def Bits.bench(n: Nat) -> U32:
  match Nat.copy(n):
    case ((n1, e1), (n2, e2)):
      Bits.mix(Bits.hash(Bits.run(n1, Bits.init()), Bits.seed()), U32.from_nat(n2))

def size.small() -> Nat:
  10n

def expect.small() -> U32:
  u32d(1238n, 295n, 167n)

def size.big() -> Nat:
  Nat.mul(1000n, Nat.mul(40n, Nat.mul(5n, 691n)))

def expect.big() -> U32:
  u32d(821n, 729n, 565n)

def main() -> Bool:
  U32.is_eq(Bits.bench(size.small()), expect.small())
