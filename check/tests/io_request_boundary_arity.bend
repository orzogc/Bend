# io (io_request_boundary_arity): the event loop's request buffer
# holds any emitted arity. A foreign def compiles to a request ctor
# of arity live-params + 1 (the continuation), and io_loop takes the
# fields into a stack buffer sized 256 -- the range of the u8 arity
# tables, whose emitter dies past 255. Before this pin the buffer
# held 8 Terms, so a foreign def with 8 or more parameters wrote
# past it: this program, at the boundary (254 parameters, request
# arity 255, the largest the emitter accepts), aborted the C lanes
# on the stack canary while the interpreter and --js printed the
# sum. All four lanes now print the same bytes. The test builds
# standalone: the suite's shard respells the def as
# t_io_request_boundary_arity_wide_sum, and the .c companion
# registers through macros spelled at the def's own name.
import Base

assert wide_sum:
  forall a0: U32
  forall a1: U32
  forall a2: U32
  forall a3: U32
  forall a4: U32
  forall a5: U32
  forall a6: U32
  forall a7: U32
  forall a8: U32
  forall a9: U32
  forall a10: U32
  forall a11: U32
  forall a12: U32
  forall a13: U32
  forall a14: U32
  forall a15: U32
  forall a16: U32
  forall a17: U32
  forall a18: U32
  forall a19: U32
  forall a20: U32
  forall a21: U32
  forall a22: U32
  forall a23: U32
  forall a24: U32
  forall a25: U32
  forall a26: U32
  forall a27: U32
  forall a28: U32
  forall a29: U32
  forall a30: U32
  forall a31: U32
  forall a32: U32
  forall a33: U32
  forall a34: U32
  forall a35: U32
  forall a36: U32
  forall a37: U32
  forall a38: U32
  forall a39: U32
  forall a40: U32
  forall a41: U32
  forall a42: U32
  forall a43: U32
  forall a44: U32
  forall a45: U32
  forall a46: U32
  forall a47: U32
  forall a48: U32
  forall a49: U32
  forall a50: U32
  forall a51: U32
  forall a52: U32
  forall a53: U32
  forall a54: U32
  forall a55: U32
  forall a56: U32
  forall a57: U32
  forall a58: U32
  forall a59: U32
  forall a60: U32
  forall a61: U32
  forall a62: U32
  forall a63: U32
  forall a64: U32
  forall a65: U32
  forall a66: U32
  forall a67: U32
  forall a68: U32
  forall a69: U32
  forall a70: U32
  forall a71: U32
  forall a72: U32
  forall a73: U32
  forall a74: U32
  forall a75: U32
  forall a76: U32
  forall a77: U32
  forall a78: U32
  forall a79: U32
  forall a80: U32
  forall a81: U32
  forall a82: U32
  forall a83: U32
  forall a84: U32
  forall a85: U32
  forall a86: U32
  forall a87: U32
  forall a88: U32
  forall a89: U32
  forall a90: U32
  forall a91: U32
  forall a92: U32
  forall a93: U32
  forall a94: U32
  forall a95: U32
  forall a96: U32
  forall a97: U32
  forall a98: U32
  forall a99: U32
  forall a100: U32
  forall a101: U32
  forall a102: U32
  forall a103: U32
  forall a104: U32
  forall a105: U32
  forall a106: U32
  forall a107: U32
  forall a108: U32
  forall a109: U32
  forall a110: U32
  forall a111: U32
  forall a112: U32
  forall a113: U32
  forall a114: U32
  forall a115: U32
  forall a116: U32
  forall a117: U32
  forall a118: U32
  forall a119: U32
  forall a120: U32
  forall a121: U32
  forall a122: U32
  forall a123: U32
  forall a124: U32
  forall a125: U32
  forall a126: U32
  forall a127: U32
  forall a128: U32
  forall a129: U32
  forall a130: U32
  forall a131: U32
  forall a132: U32
  forall a133: U32
  forall a134: U32
  forall a135: U32
  forall a136: U32
  forall a137: U32
  forall a138: U32
  forall a139: U32
  forall a140: U32
  forall a141: U32
  forall a142: U32
  forall a143: U32
  forall a144: U32
  forall a145: U32
  forall a146: U32
  forall a147: U32
  forall a148: U32
  forall a149: U32
  forall a150: U32
  forall a151: U32
  forall a152: U32
  forall a153: U32
  forall a154: U32
  forall a155: U32
  forall a156: U32
  forall a157: U32
  forall a158: U32
  forall a159: U32
  forall a160: U32
  forall a161: U32
  forall a162: U32
  forall a163: U32
  forall a164: U32
  forall a165: U32
  forall a166: U32
  forall a167: U32
  forall a168: U32
  forall a169: U32
  forall a170: U32
  forall a171: U32
  forall a172: U32
  forall a173: U32
  forall a174: U32
  forall a175: U32
  forall a176: U32
  forall a177: U32
  forall a178: U32
  forall a179: U32
  forall a180: U32
  forall a181: U32
  forall a182: U32
  forall a183: U32
  forall a184: U32
  forall a185: U32
  forall a186: U32
  forall a187: U32
  forall a188: U32
  forall a189: U32
  forall a190: U32
  forall a191: U32
  forall a192: U32
  forall a193: U32
  forall a194: U32
  forall a195: U32
  forall a196: U32
  forall a197: U32
  forall a198: U32
  forall a199: U32
  forall a200: U32
  forall a201: U32
  forall a202: U32
  forall a203: U32
  forall a204: U32
  forall a205: U32
  forall a206: U32
  forall a207: U32
  forall a208: U32
  forall a209: U32
  forall a210: U32
  forall a211: U32
  forall a212: U32
  forall a213: U32
  forall a214: U32
  forall a215: U32
  forall a216: U32
  forall a217: U32
  forall a218: U32
  forall a219: U32
  forall a220: U32
  forall a221: U32
  forall a222: U32
  forall a223: U32
  forall a224: U32
  forall a225: U32
  forall a226: U32
  forall a227: U32
  forall a228: U32
  forall a229: U32
  forall a230: U32
  forall a231: U32
  forall a232: U32
  forall a233: U32
  forall a234: U32
  forall a235: U32
  forall a236: U32
  forall a237: U32
  forall a238: U32
  forall a239: U32
  forall a240: U32
  forall a241: U32
  forall a242: U32
  forall a243: U32
  forall a244: U32
  forall a245: U32
  forall a246: U32
  forall a247: U32
  forall a248: U32
  forall a249: U32
  forall a250: U32
  forall a251: U32
  forall a252: U32
  forall a253: U32
  IO(U32)

def wide_sum(
  a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
  a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25,
  a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38,
  a39, a40, a41, a42, a43, a44, a45, a46, a47, a48, a49, a50, a51,
  a52, a53, a54, a55, a56, a57, a58, a59, a60, a61, a62, a63, a64,
  a65, a66, a67, a68, a69, a70, a71, a72, a73, a74, a75, a76, a77,
  a78, a79, a80, a81, a82, a83, a84, a85, a86, a87, a88, a89, a90,
  a91, a92, a93, a94, a95, a96, a97, a98, a99, a100, a101, a102, a103,
  a104, a105, a106, a107, a108, a109, a110, a111, a112, a113, a114, a115, a116,
  a117, a118, a119, a120, a121, a122, a123, a124, a125, a126, a127, a128, a129,
  a130, a131, a132, a133, a134, a135, a136, a137, a138, a139, a140, a141, a142,
  a143, a144, a145, a146, a147, a148, a149, a150, a151, a152, a153, a154, a155,
  a156, a157, a158, a159, a160, a161, a162, a163, a164, a165, a166, a167, a168,
  a169, a170, a171, a172, a173, a174, a175, a176, a177, a178, a179, a180, a181,
  a182, a183, a184, a185, a186, a187, a188, a189, a190, a191, a192, a193, a194,
  a195, a196, a197, a198, a199, a200, a201, a202, a203, a204, a205, a206, a207,
  a208, a209, a210, a211, a212, a213, a214, a215, a216, a217, a218, a219, a220,
  a221, a222, a223, a224, a225, a226, a227, a228, a229, a230, a231, a232, a233,
  a234, a235, a236, a237, a238, a239, a240, a241, a242, a243, a244, a245, a246,
  a247, a248, a249, a250, a251, a252, a253):
  import "./io_request_boundary_arity.c"
  import "./io_request_boundary_arity.js"

assert main:
  IO(Unit)

def main():
  do IO<Unit>:
    x : U32 <- wide_sum(
      1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
      20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37,
      38,
      39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56,
      57,
      58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75,
      76,
      77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94,
      95,
      96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110,
      111, 112, 113, 114,
      115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128,
      129, 130, 131, 132, 133,
      134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
      148, 149, 150, 151, 152,
      153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166,
      167, 168, 169, 170, 171,
      172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185,
      186, 187, 188, 189, 190,
      191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204,
      205, 206, 207, 208, 209,
      210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223,
      224, 225, 226, 227, 228,
      229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242,
      243, 244, 245, 246, 247,
      248, 249, 250, 251, 252, 253, 254)
    IO.print(U32.show(x))
$$ bend %
32385
$$ bend % --seq
32385
exit 0
$$ bend % --par
32385
exit 0
$$ bend % --js
32385
exit 0
