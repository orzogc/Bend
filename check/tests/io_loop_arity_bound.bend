# io (io_loop_arity_bound): the event loop's field buffer holds the
# largest arity the emitter admits. The arity tables are byte tables,
# so an arity tops at 255: main's IO action here is an under-saturated
# spine of a 255-ary def, and io_loop must take its 254 captured words
# out before it can run the action. Before this pin the loop read the
# fields into Term fs[8], so any op or request past eight fields wrote
# past the buffer: this program smashed the loop's own frame in both C
# lanes (SIGABRT, no output). Now fs holds any byte arity.
import Base

assert act:
  forall a001: U32
  forall a002: U32
  forall a003: U32
  forall a004: U32
  forall a005: U32
  forall a006: U32
  forall a007: U32
  forall a008: U32
  forall a009: U32
  forall a010: U32
  forall a011: U32
  forall a012: U32
  forall a013: U32
  forall a014: U32
  forall a015: U32
  forall a016: U32
  forall a017: U32
  forall a018: U32
  forall a019: U32
  forall a020: U32
  forall a021: U32
  forall a022: U32
  forall a023: U32
  forall a024: U32
  forall a025: U32
  forall a026: U32
  forall a027: U32
  forall a028: U32
  forall a029: U32
  forall a030: U32
  forall a031: U32
  forall a032: U32
  forall a033: U32
  forall a034: U32
  forall a035: U32
  forall a036: U32
  forall a037: U32
  forall a038: U32
  forall a039: U32
  forall a040: U32
  forall a041: U32
  forall a042: U32
  forall a043: U32
  forall a044: U32
  forall a045: U32
  forall a046: U32
  forall a047: U32
  forall a048: U32
  forall a049: U32
  forall a050: U32
  forall a051: U32
  forall a052: U32
  forall a053: U32
  forall a054: U32
  forall a055: U32
  forall a056: U32
  forall a057: U32
  forall a058: U32
  forall a059: U32
  forall a060: U32
  forall a061: U32
  forall a062: U32
  forall a063: U32
  forall a064: U32
  forall a065: U32
  forall a066: U32
  forall a067: U32
  forall a068: U32
  forall a069: U32
  forall a070: U32
  forall a071: U32
  forall a072: U32
  forall a073: U32
  forall a074: U32
  forall a075: U32
  forall a076: U32
  forall a077: U32
  forall a078: U32
  forall a079: U32
  forall a080: U32
  forall a081: U32
  forall a082: U32
  forall a083: U32
  forall a084: U32
  forall a085: U32
  forall a086: U32
  forall a087: U32
  forall a088: U32
  forall a089: U32
  forall a090: U32
  forall a091: U32
  forall a092: U32
  forall a093: U32
  forall a094: U32
  forall a095: U32
  forall a096: U32
  forall a097: U32
  forall a098: U32
  forall a099: U32
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
  forall a254: U32
  forall -R: Type
  forall k: U32 -> IO.OP<R>
  IO.OP<R>

def act(
  a001, a002, a003, a004, a005, a006, a007, a008,
  a009, a010, a011, a012, a013, a014, a015, a016,
  a017, a018, a019, a020, a021, a022, a023, a024,
  a025, a026, a027, a028, a029, a030, a031, a032,
  a033, a034, a035, a036, a037, a038, a039, a040,
  a041, a042, a043, a044, a045, a046, a047, a048,
  a049, a050, a051, a052, a053, a054, a055, a056,
  a057, a058, a059, a060, a061, a062, a063, a064,
  a065, a066, a067, a068, a069, a070, a071, a072,
  a073, a074, a075, a076, a077, a078, a079, a080,
  a081, a082, a083, a084, a085, a086, a087, a088,
  a089, a090, a091, a092, a093, a094, a095, a096,
  a097, a098, a099, a100, a101, a102, a103, a104,
  a105, a106, a107, a108, a109, a110, a111, a112,
  a113, a114, a115, a116, a117, a118, a119, a120,
  a121, a122, a123, a124, a125, a126, a127, a128,
  a129, a130, a131, a132, a133, a134, a135, a136,
  a137, a138, a139, a140, a141, a142, a143, a144,
  a145, a146, a147, a148, a149, a150, a151, a152,
  a153, a154, a155, a156, a157, a158, a159, a160,
  a161, a162, a163, a164, a165, a166, a167, a168,
  a169, a170, a171, a172, a173, a174, a175, a176,
  a177, a178, a179, a180, a181, a182, a183, a184,
  a185, a186, a187, a188, a189, a190, a191, a192,
  a193, a194, a195, a196, a197, a198, a199, a200,
  a201, a202, a203, a204, a205, a206, a207, a208,
  a209, a210, a211, a212, a213, a214, a215, a216,
  a217, a218, a219, a220, a221, a222, a223, a224,
  a225, a226, a227, a228, a229, a230, a231, a232,
  a233, a234, a235, a236, a237, a238, a239, a240,
  a241, a242, a243, a244, a245, a246, a247, a248,
  a249, a250, a251, a252, a253, a254,
  R, k):
  s1 = {
    a001 + a002 + a003 + a004 + a005 + a006 + a007 + a008 +
    a009 + a010 + a011 + a012 + a013 + a014 + a015 + a016 +
    a017 + a018 + a019 + a020 + a021 + a022 + a023 + a024 +
    a025 + a026 + a027 + a028 + a029 + a030 + a031 + a032 :
    U32}
  s2 = {
    a033 + a034 + a035 + a036 + a037 + a038 + a039 + a040 +
    a041 + a042 + a043 + a044 + a045 + a046 + a047 + a048 +
    a049 + a050 + a051 + a052 + a053 + a054 + a055 + a056 +
    a057 + a058 + a059 + a060 + a061 + a062 + a063 + a064 :
    U32}
  s3 = {
    a065 + a066 + a067 + a068 + a069 + a070 + a071 + a072 +
    a073 + a074 + a075 + a076 + a077 + a078 + a079 + a080 +
    a081 + a082 + a083 + a084 + a085 + a086 + a087 + a088 +
    a089 + a090 + a091 + a092 + a093 + a094 + a095 + a096 :
    U32}
  s4 = {
    a097 + a098 + a099 + a100 + a101 + a102 + a103 + a104 +
    a105 + a106 + a107 + a108 + a109 + a110 + a111 + a112 +
    a113 + a114 + a115 + a116 + a117 + a118 + a119 + a120 +
    a121 + a122 + a123 + a124 + a125 + a126 + a127 + a128 :
    U32}
  s5 = {
    a129 + a130 + a131 + a132 + a133 + a134 + a135 + a136 +
    a137 + a138 + a139 + a140 + a141 + a142 + a143 + a144 +
    a145 + a146 + a147 + a148 + a149 + a150 + a151 + a152 +
    a153 + a154 + a155 + a156 + a157 + a158 + a159 + a160 :
    U32}
  s6 = {
    a161 + a162 + a163 + a164 + a165 + a166 + a167 + a168 +
    a169 + a170 + a171 + a172 + a173 + a174 + a175 + a176 +
    a177 + a178 + a179 + a180 + a181 + a182 + a183 + a184 +
    a185 + a186 + a187 + a188 + a189 + a190 + a191 + a192 :
    U32}
  s7 = {
    a193 + a194 + a195 + a196 + a197 + a198 + a199 + a200 +
    a201 + a202 + a203 + a204 + a205 + a206 + a207 + a208 +
    a209 + a210 + a211 + a212 + a213 + a214 + a215 + a216 +
    a217 + a218 + a219 + a220 + a221 + a222 + a223 + a224 :
    U32}
  s8 = {
    a225 + a226 + a227 + a228 + a229 + a230 + a231 + a232 +
    a233 + a234 + a235 + a236 + a237 + a238 + a239 + a240 +
    a241 + a242 + a243 + a244 + a245 + a246 + a247 + a248 +
    a249 + a250 + a251 + a252 + a253 + a254 :
    U32}
  s = {s1 + s2 + s3 + s4 + s5 + s6 + s7 + s8 : U32}
  IO.print(U32.show(s), R, u => k(0))

assert main:
  IO(U32)

def main():
  act(
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
    17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
    33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
    49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64,
    65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80,
    81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96,
    97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112,
    113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128,
    129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144,
    145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160,
    161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176,
    177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192,
    193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208,
    209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
    225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240,
    241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254)
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
