#[halts]
import Base
# Merkle: Merkle tree over an encrypted counter stream, with a proof
# phase, ported 1-to-1 from Bend3's par_merkle. 2^d leaves; each leaf Speck32/64-encrypts
# its BLOCKS (30) counter blocks (22 ARX rounds per block, the standard
# test-vector key expanded offline into the rk table) and chains the
# ciphertexts into a leaf hash; build materializes the actual Merkle
# tree (every Mn node stores mrk of its children), audit re-folds the
# tree checking every stored hash (a mismatch perturbs the result), and
# pgen extracts the Merkle proof for leaf PROBE by recomputing each
# sibling subtree hash with the pure scalar htree prover -- pverify
# then folds the Path back up from the probed leaf hash. The checksum
# is mrk(audit root, recomputed root). Round and block counters are
# Nats (no U32 match in Bend4); rk indexes by Nat literals.
#
# Sizes (d, probe), blocks fixed at 30: small (4, 13) expect 524568222
# (verified against a Bend3 C run on the cluster), big (22, 1337)
# expect 3104235417 (from the Bend3 header).

type Mt:
  Ml{h: U32}
  Mn{h: U32, l: Mt, r: Mt}

type Path:
  Pn{}
  Pc{side: U32, sib: U32, rest: Path}

def blocks() -> Nat:
  30n

def sel(t: U32, x: U32, y: U32) -> U32:
  match U32.is_zero(t):
    case True{}:
      x
    case False{}:
      y

# Speck32/64 round keys for key 1918 1110 0908 0100
def rk(j: Nat) -> U32:
  match j:
    case 0n:
      256
    case 1n:
      5394
    case 2n:
      24957
    case 3n:
      5208
    case 4n:
      26905
    case 5n:
      30690
    case 6n:
      3209
    case 7n:
      52443
    case 8n:
      61418
    case 9n:
      20019
    case 10n:
      30452
    case 11n:
      22902
    case 12n:
      61067
    case 13n:
      56068
    case 14n:
      17943
    case 15n:
      62334
    case 16n:
      34740
    case 17n:
      36554
    case 18n:
      60827
    case 19n:
      14930
    case 20n:
      33321
    case 21n+p:
      60772

# 22 Speck rounds over the 16-bit halves x, y (n counts down, j up)
def spk(n: Nat, +j: Nat, +x: U32, +y: U32) -> U32:
  match n:
    case 0n:
      U32.or(x, U32.shln(16n, y))
    case 1n+p:
      +nx = U32.and(U32.xor(U32.and(U32.add(U32.and(U32.or(U32.shrn(7n, x), U32.shln(9n, x)), 65535), y), 65535), rk(j)), 65535)
      spk(p, 1n+j, nx, U32.and(U32.xor(U32.and(U32.or(U32.shln(2n, y), U32.shrn(14n, y)), 65535), nx), 65535))

# one leaf: encrypt BLOCKS counter blocks, chain the ciphertexts
def blk(j: Nat, +b: U32, acc: U32) -> U32:
  match j:
    case 0n:
      acc
    case 1n+p:
      ct = spk(22n, 0n, U32.and(b, 65535), U32.and(U32.shrn(16n, b), 65535))
      blk(p, U32.inc(b), U32.add(U32.mul(acc, 2654435761), ct))

def leafh(+b: U32) -> U32:
  blk(blocks(), U32.mul(b, U32.from_nat(blocks())), U32.inc(b))

# Merkle join: ARX mix of the two child hashes
def mrk(a: U32, b: U32) -> U32:
  +hh = U32.xor(U32.mul(a, 2654435761), b)
  +h2 = U32.xor(U32.mul(U32.add(hh, 2246822519), 2246822519), U32.shrn(13n, hh))
  U32.xor(h2, U32.shrn(16n, h2))

# the scalar prover: recompute a subtree hash without materializing it
def htree(+d: Nat, +b: U32) -> U32:
  match d:
    case 0n:
      leafh(b)
    case 1n+p:
      Both{a, c} = {Both{htree(p, b), htree(p, U32.add(b, U32.shln(p, 1)))} : Par<U32, U32>}
      mrk(a, c)

# join two subtrees into a hashed node (peek the child hashes, rebuild)
def mjoin(l: Mt, r: Mt) -> Mt:
  match l r:
    case Ml{a} Ml{b}:
      +aa = a
      +bb = b
      Mn{mrk(aa, bb), Ml{aa}, Ml{bb}}
    case Ml{a} Mn{c, x, y}:
      +aa = a
      +cc = c
      Mn{mrk(aa, cc), Ml{aa}, Mn{cc, x, y}}
    case Mn{a, x, y} Ml{b}:
      +aa = a
      +bb = b
      Mn{mrk(aa, bb), Mn{aa, x, y}, Ml{bb}}
    case Mn{a, x, y} Mn{c, w, z}:
      +aa = a
      +cc = c
      Mn{mrk(aa, cc), Mn{aa, x, y}, Mn{cc, w, z}}

# build the Merkle tree over blocks b .. b + 2^d - 1
def build(+d: Nat, +b: U32) -> Mt:
  match d:
    case 0n:
      Ml{leafh(b)}
    case 1n+p:
      Both{l, r} = {Both{build(p, b), build(p, U32.add(b, U32.shln(p, 1)))} : Par<Mt, Mt>}
      mjoin(l, r)

# audit: re-fold the tree; any stored-hash mismatch perturbs the result
def audit(t: Mt) -> U32:
  match t:
    case Ml{h}:
      h
    case Mn{h, l, r}:
      Both{a, b} = {Both{audit(l), audit(r)} : Par<U32, U32>}
      +m = mrk(a, b)
      U32.add(m, U32.xor(m, h))

# Merkle proof for leaf k: per level, the side bit and the sibling hash
# (recomputed by the scalar prover; the ladder forks each sibling)
def pgen(+d: Nat, +k: U32, +b: U32) -> Path:
  match d:
    case 0n:
      Pn{}
    case 1n+p:
      Both{bit0, half0} = {Both{U32.and(U32.shrn(p, k), 1), U32.shln(p, 1)} : Par<U32, U32>}
      +bit = bit0
      +half = half0
      Both{sib, rest} = {Both{htree(p, sel(bit, U32.add(b, half), b)), pgen(p, k, sel(bit, b, U32.add(b, half)))} : Par<U32, Path>}
      Pc{bit, sib, rest}

# fold the proof back up from the leaf hash to a root hash
def pverify(p: Path, lh: U32) -> U32:
  match p:
    case Pn{}:
      lh
    case Pc{s, sib, rest}:
      +ss = s
      +hh = pverify(rest, lh)
      +sb = sib
      mrk(sel(ss, hh, sb), sel(ss, sb, hh))

# small: (4n, 13) expect 524568222; big (22n, 1337) expect 3104235417
def main() -> U32:
  t = build!(22n, 0)
  root = audit!(t)
  mrk(root, pverify(pgen!(22n, 1337, 0), leafh(1337)))
