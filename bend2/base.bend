# Types
# =====

# Data
# ----

type Empty is Data:

type Unit is Data:
  Unit{}

type Bool is Data:
  False{}
  True{}

type Cmp is Data:
  LT{}
  EQ{}
  GT{}

type Either<a, b, -A: Kind(a), -B: Kind(b)> is Kind(a <&> b):
  Inl{value: A}
  Inr{value: B}

type Sigma<a, b, -A: Kind(a), -B: @-x: A -> Kind(b)> is Kind(a <&> b):
  Tuple{fst: A, snd: B(fst)}

type Nat is Data:
  Zero{}
  Succ{pred: Nat}

type Maybe<a, -A: Kind(a)> is Kind(a):
  None{}
  Some{value: A}

type Result<a, b, -E: Kind(a), -A: Kind(b)> is Kind(a <&> b):
  Fail{error: E}
  Done{value: A}

type List<a, -A: Kind(a)> is Kind(a):
  Nil{}
  Con{head: A, tail: List<a, A>}

type Array<-T: Type> is Type:
  ALeaf{value: T}
  ANode{xs: Array<T>, ys: Array<T>}

assert Word:
  forall n: Nat
  Data

type Word.Nil is Data:
  WNil{}

type Word.Con<-p: Nat> is Data:
  WCon{head: Bool, tail: Word(p)}

type U32 is Data:
  U32{data: Word(32n)}

type F32 is Data:
  F32{data: Word(32n)}

type Char is Data:
  Chr{code: U32}

type String is Data:
  SNil{}
  SCon{head: Char, tail: String}

# Effects
# -------

type File is Type:
  File{slot: U32, gen: U32}

type Socket is Type:
  Socket{slot: U32, gen: U32}

type Listener is Type:
  Listener{slot: U32, gen: U32}

type IO.OP<-R: Type> is Type:
  Emit{value: R}
  Halt{code: U32, message: String}

# Map
# ---

type Map<a, -V: Kind(a)> is Kind(a):
  MTip{}
  MLeaf{key: String, val: V}
  MNode{pos: Nat, lo: Map<a, V>, hi: Map<a, V>}

# Sugars
# ------

# Claims
# ======

# Pair
# ----

assert Pair:
  forall -A: Type
  forall -B: Type
  Type

assert Exists:
  forall -A: Type
  forall -B: @-x: A -> Type
  Type

assert Or:
  forall -A: Type
  forall -B: Type
  Type

# Effects
# -------

assert IO:
  forall -A: Type
  Type

assert IO.pure:
  forall -A: Type
  forall x: A
  IO(A)

assert IO.bind:
  forall -A: Type
  forall -B: Type
  forall m: IO(A)
  forall f: A -> IO(B)
  IO(B)

assert IO.print:
  forall text: String
  IO(Unit)

assert IO.write:
  forall text: String
  IO(Unit)

assert IO.print_err:
  forall text: String
  IO(Unit)

assert IO.get_env:
  forall name: String
  IO(Result<&1, &1, U32 & String, String>)

assert IO.die:
  forall -A: Type
  forall code: U32
  forall message: String
  IO(A)

assert IO.pass:
  forall -A: Type
  forall r: Result<&1, &1, U32 & String, A>
  IO(A)

assert IO.try:
  forall -A: Type
  forall action: IO(Result<&1, &1, U32 & String, A>)
  IO(A)

assert File.open:
  forall path: String
  forall mode: String
  IO(Result<&1, &1, U32 & String, File>)

assert File.read:
  forall file: File
  forall max: U32
  IO(File & Result<&1, &1, U32 & String, String>)

assert File.write:
  forall file: File
  forall data: String
  IO(File & Result<&1, &1, U32 & String, Unit>)

assert File.close:
  forall file: File
  IO(Unit)

assert TCP.listen:
  forall port: U32
  IO(Result<&1, &1, U32 & String, Listener>)

assert TCP.accept:
  forall listener: Listener
  IO(Listener & Result<&1, &1, U32 & String, Socket>)

assert TCP.connect:
  forall host: String
  forall port: U32
  IO(Result<&1, &1, U32 & String, Socket>)

assert TCP.send:
  forall socket: Socket
  forall data: String
  IO(Socket & Result<&1, &1, U32 & String, Unit>)

assert TCP.recv:
  forall socket: Socket
  forall max: U32
  IO(Socket & Result<&1, &1, U32 & String, String>)

assert UDP.bind:
  forall port: U32
  IO(Result<&1, &1, U32 & String, Socket>)

assert UDP.send_to:
  forall socket: Socket
  forall host: String
  forall port: U32
  forall data: String
  IO(Socket & Result<&1, &1, U32 & String, Unit>)

assert UDP.recv_from:
  forall socket: Socket
  forall max: U32
  IO(Socket & Result<&1, &1, U32 & String, String & U32 & String>)

assert Socket.close:
  forall socket: Socket
  IO(Unit)

assert Listener.close:
  forall listener: Listener
  IO(Unit)

# Equal
# -----

assert Equal.cong:
  forall -A: Type
  forall -B: Type
  forall -f: A -> B
  forall -a: A
  forall -b: A
  forall e: {a == b : A}
  {f(a) == f(b) : B}

assert Equal.sym:
  forall -A: Type
  forall -a: A
  forall -b: A
  forall e: {a == b : A}
  {b == a : A}

assert Equal.trans:
  forall -A: Type
  forall -a: A
  forall -b: A
  forall -c: A
  forall ab: {a == b : A}
  forall bc: {b == c : A}
  {a == c : A}

# Empty
# -----

assert Empty.absurd:
  forall -A: Type
  forall e: Empty
  A

# Bool
# ----

assert Bool.not:
  forall b: Bool
  Bool

assert Bool.and:
  forall a: Bool
  forall b: Bool
  Bool

assert Bool.or:
  forall a: Bool
  forall b: Bool
  Bool

assert Bool.xor:
  forall a: Bool
  forall b: Bool
  Bool

assert Bool.cmp:
  forall a: Bool
  forall b: Bool
  Cmp

assert Bool.full_add:
  forall a: Bool
  forall b: Bool
  forall c: Bool
  Bool & Bool

# Cmp
# ---

assert Cmp.is_lt:
  forall c: Cmp
  Bool

assert Cmp.is_eq:
  forall c: Cmp
  Bool

assert Cmp.is_gt:
  forall c: Cmp
  Bool

assert Cmp.is_le:
  forall c: Cmp
  Bool

assert Cmp.is_ge:
  forall c: Cmp
  Bool

# Nat
# ---

assert Nat.double:
  forall n: Nat
  Nat

assert Nat.add:
  forall a: Nat
  forall b: Nat
  Nat

assert Nat.sub:
  forall a: Nat
  forall b: Nat
  Nat

assert Nat.mul:
  forall a: Nat
  forall +b: Nat
  Nat

assert Nat.divmod.go:
  forall n: Nat
  forall m: Nat
  forall d: Nat
  forall r: Nat
  Nat & Nat

assert Nat.divmod:
  forall a: Nat
  forall b: Nat
  Nat & Nat

assert Nat.cmp:
  forall a: Nat
  forall b: Nat
  Cmp

assert Nat.is_lt:
  forall a: Nat
  forall b: Nat
  Bool

# Maybe
# -----

assert Maybe.pure:
  forall -a: Quant
  forall -A: Kind(a)
  forall x: A
  Maybe<a, A>

assert Maybe.bind:
  forall -a: Quant
  forall -A: Kind(a)
  forall -B: Kind(a)
  forall m: Maybe<a, A>
  forall f: A -> Maybe<a, B>
  Maybe<a, B>

# Result
# ------

assert Result.pure:
  forall -a: Quant
  forall -b: Quant
  forall -E: Kind(a)
  forall -A: Kind(b)
  forall x: A
  Result<a, b, E, A>

assert Result.fail:
  forall -a: Quant
  forall -b: Quant
  forall -E: Kind(a)
  forall -A: Kind(b)
  forall e: E
  Result<a, b, E, A>

assert Result.bind:
  forall -a: Quant
  forall -b: Quant
  forall -E: Kind(a)
  forall -A: Kind(b)
  forall -B: Kind(b)
  forall r: Result<a, b, E, A>
  forall f: A -> Result<a, b, E, B>
  Result<a, b, E, B>

# Word
# ----

assert Word.cast:
  forall -m: Nat
  forall -n: Nat
  forall e: {m == n : Nat}
  forall w: Word(m)
  Word(n)

assert Word.zero:
  forall n: Nat
  Word(n)

assert Word.not:
  forall n: Nat
  forall w: Word(n)
  Word(n)

assert Word.and:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  Word(n)

assert Word.or:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  Word(n)

assert Word.xor:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  Word(n)

assert Word.shl.put:
  forall n: Nat
  forall c: Bool
  forall w: Word(n)
  Word(n)

assert Word.shl:
  forall n: Nat
  forall w: Word(n)
  Word(n)

assert Word.shl.out.con:
  forall -p: Nat
  forall c: Bool
  forall r: Bool & Word(p)
  Bool & Word(1n+p)

assert Word.shl.out:
  forall n: Nat
  forall c: Bool
  forall w: Word(n)
  Bool & Word(n)

assert Word.shr.pad:
  forall n: Nat
  forall w: Word(n)
  Word(1n+n)

assert Word.shr:
  forall n: Nat
  forall w: Word(n)
  Word(n)

assert Word.cmp.fin:
  forall ab: Bool
  forall bb: Bool
  forall t: Cmp
  Cmp

assert Word.cmp:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  Cmp

assert Word.inc:
  forall n: Nat
  forall w: Word(n)
  Word(n)

assert Word.adc.con:
  forall p: Nat
  forall at: Word(p)
  forall bt: Word(p)
  forall f: Bool
  forall sk: Bool & Bool
  Word(1n+p)

assert Word.adc:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  forall f: Bool
  forall c: Bool
  Word(n)

assert Word.add:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  Word(n)

assert Word.sub:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  Word(n)

assert Word.add_comm.arm:
  forall p: Nat
  forall -h: Bool
  forall at: Word(p)
  forall bt: Word(p)
  forall k: Bool
  {WCon{h, Word.adc(p, at, bt, False{}, k)}
    == WCon{h, Word.adc(p, bt, at, False{}, k)} : Word.Con<p>}

assert Word.add_comm.go:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  forall c: Bool
  {Word.adc(n, a, b, False{}, c) == Word.adc(n, b, a, False{}, c) : Word(n)}

assert Word.add_comm:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  {Word.add(n, a, b) == Word.add(n, b, a) : Word(n)}

assert Word.to_nat:
  forall n: Nat
  forall w: Word(n)
  Nat

assert Word.mul.go:
  forall +n: Nat
  forall m: Nat
  forall a: Word(m)
  forall b: Word(n)
  forall acc: Word(n)
  Word(n)

assert Word.mul:
  forall +n: Nat
  forall a: Word(n)
  forall b: Word(n)
  Word(n)

# U32
# ---

assert U32.zero:
  U32

assert U32.one:
  U32

assert U32.inc:
  forall a: U32
  U32

assert U32.add:
  forall a: U32
  forall b: U32
  U32

assert U32.add_comm:
  forall a: U32
  forall b: U32
  {U32.add(a, b) == U32.add(b, a) : U32}

assert U32.sub:
  forall a: U32
  forall b: U32
  U32

assert U32.mul:
  forall a: U32
  forall b: U32
  U32

assert U32.not:
  forall a: U32
  U32

assert U32.and:
  forall a: U32
  forall b: U32
  U32

assert U32.or:
  forall a: U32
  forall b: U32
  U32

assert U32.xor:
  forall a: U32
  forall b: U32
  U32

assert U32.shl:
  forall a: U32
  U32

assert U32.shr:
  forall a: U32
  U32

assert U32.shln:
  forall a: U32
  forall n: Nat
  U32

assert U32.shrn:
  forall a: U32
  forall n: Nat
  U32

assert U32.cmp:
  forall a: U32
  forall b: U32
  Cmp

assert U32.is_eq:
  forall a: U32
  forall b: U32
  Bool

assert U32.is_ne:
  forall a: U32
  forall b: U32
  Bool

assert U32.is_lt:
  forall a: U32
  forall b: U32
  Bool

assert U32.is_le:
  forall a: U32
  forall b: U32
  Bool

assert U32.is_gt:
  forall a: U32
  forall b: U32
  Bool

assert U32.is_ge:
  forall a: U32
  forall b: U32
  Bool

assert U32.is_zero:
  forall a: U32
  Bool

assert U32.to_nat:
  forall a: U32
  Nat

assert U32.from_nat:
  forall n: Nat
  U32

assert U32.divmod.go.fin:
  forall -p: Nat
  forall q: Word(p)
  forall s: U32
  forall b: U32
  forall g: Bool
  Word(1n+p) & U32

assert U32.divmod.go.shl:
  forall -p: Nat
  forall q: Word(p)
  forall +b: U32
  forall ts: Bool & Word(32n)
  Word(1n+p) & U32

assert U32.divmod.go.rec:
  forall -p: Nat
  forall a0: Bool
  forall +b: U32
  forall qr: Word(p) & U32
  Word(1n+p) & U32

assert U32.divmod.go:
  forall m: Nat
  forall a: Word(m)
  forall +b: U32
  Word(m) & U32

assert U32.div.fin:
  forall qr: Word(32n) & U32
  U32

assert U32.div.if:
  forall aw: Word(32n)
  forall b: U32
  forall z: Bool
  U32

assert U32.div:
  forall a: U32
  forall +b: U32
  U32

assert U32.mod.fin:
  forall qr: Word(32n) & U32
  U32

assert U32.mod.if:
  forall aw: Word(32n)
  forall b: U32
  forall z: Bool
  U32

assert U32.mod:
  forall a: U32
  forall +b: U32
  U32

# F32
# ---

assert U32.to_f32:
  forall a: U32
  F32

assert F32.to_u32:
  forall a: F32
  U32

assert F32.add:
  forall a: F32
  forall b: F32
  F32

assert F32.sub:
  forall a: F32
  forall b: F32
  F32

assert F32.mul:
  forall a: F32
  forall b: F32
  F32

assert F32.div:
  forall a: F32
  forall b: F32
  F32

assert F32.mod:
  forall a: F32
  forall b: F32
  F32

assert F32.pow:
  forall a: F32
  forall b: F32
  F32

assert F32.atan2:
  forall a: F32
  forall b: F32
  F32

assert F32.neg:
  forall a: F32
  F32

assert F32.abs:
  forall a: F32
  F32

assert F32.sqrt:
  forall a: F32
  F32

assert F32.exp:
  forall a: F32
  F32

assert F32.log:
  forall a: F32
  F32

assert F32.log2:
  forall a: F32
  F32

assert F32.log10:
  forall a: F32
  F32

assert F32.sin:
  forall a: F32
  F32

assert F32.cos:
  forall a: F32
  F32

assert F32.tan:
  forall a: F32
  F32

assert F32.asin:
  forall a: F32
  F32

assert F32.acos:
  forall a: F32
  F32

assert F32.atan:
  forall a: F32
  F32

assert F32.sinh:
  forall a: F32
  F32

assert F32.cosh:
  forall a: F32
  F32

assert F32.tanh:
  forall a: F32
  F32

assert F32.floor:
  forall a: F32
  F32

assert F32.ceil:
  forall a: F32
  F32

assert F32.trunc:
  forall a: F32
  F32

assert F32.is_eq:
  forall a: F32
  forall b: F32
  Bool

assert F32.is_ne:
  forall a: F32
  forall b: F32
  Bool

assert F32.is_lt:
  forall a: F32
  forall b: F32
  Bool

assert F32.is_le:
  forall a: F32
  forall b: F32
  Bool

assert F32.is_gt:
  forall a: F32
  forall b: F32
  Bool

assert F32.is_ge:
  forall a: F32
  forall b: F32
  Bool

assert F32.show:
  forall +a: F32
  String

assert F32.read:
  forall s: String
  Maybe<&2, F32>

# Char
# ----

assert Char.cmp:
  forall a: Char
  forall b: Char
  (Char & Char) & Cmp

# String
# ------

assert String.append:
  forall a: String
  forall b: String
  String

assert String.cmp.rec:
  forall h1b: Char
  forall h2b: Char
  forall rr: (String & String) & Cmp
  (String & String) & Cmp

assert String.cmp.fin:
  forall t1: String
  forall t2: String
  forall hc: (Char & Char) & Cmp
  (String & String) & Cmp

assert String.cmp:
  forall a: String
  forall b: String
  (String & String) & Cmp

assert String.eq.fin:
  forall r: (String & String) & Cmp
  Bool

assert String.eq:
  forall a: String
  forall b: String
  Bool

# Text
# ----

assert U32.read.dig.if:
  forall x: U32
  forall ok: Bool
  Maybe<&2, U32>

assert U32.read.dig:
  forall c: Char
  Maybe<&2, U32>

assert Nat.show.put:
  forall qr: Nat & Nat
  Char & Nat

assert Nat.show.step:
  forall n: Nat
  Char & Nat

assert Nat.show.fin:
  forall g: Nat
  forall acc: String
  forall dq: Char & Nat
  String

assert Nat.show.go:
  forall f: Nat
  forall n: Nat
  forall acc: String
  String

assert Nat.show:
  forall +n: Nat
  String

assert Nat.read.fin:
  forall t: String
  forall acc: Nat
  forall d: Maybe<&2, U32>
  Maybe<&2, Nat>

assert Nat.read.go:
  forall s: String
  forall acc: Nat
  Maybe<&2, Nat>

assert Nat.read:
  forall s: String
  Maybe<&2, Nat>

assert U32.show.fin:
  forall g: Nat
  forall acc: String
  forall +n: U32
  forall z: Bool
  String

assert U32.show.go:
  forall f: Nat
  forall +n: U32
  forall acc: String
  String

assert U32.show.if:
  forall a: U32
  forall z: Bool
  String

assert U32.show:
  forall +a: U32
  String

assert U32.read.fin:
  forall t: String
  forall acc: U32
  forall d: Maybe<&2, U32>
  Maybe<&2, U32>

assert U32.read.go:
  forall s: String
  forall acc: U32
  Maybe<&2, U32>

assert U32.read:
  forall s: String
  Maybe<&2, U32>

# Array
# -----

assert Array.size.node:
  forall -T: Type
  forall ys: Array<T>
  forall r: Array<T> & U32
  Array<T> & U32

assert Array.size:
  forall -T: Type
  forall a: Array<T>
  Array<T> & U32

assert Array.swap.lo:
  forall -T: Type
  forall ys: Array<T>
  forall r: Array<T> & T
  Array<T> & T

assert Array.swap.hi:
  forall -T: Type
  forall xs: Array<T>
  forall r: Array<T> & T
  Array<T> & T

assert Array.swap.if:
  forall -T: Type
  forall xs: Array<T>
  forall ys: Array<T>
  forall +h: U32
  forall i: U32
  forall v: T
  forall z: Bool
  Array<T> & T

assert Array.swap.go:
  forall -T: Type
  forall a: Array<T>
  forall n: U32
  forall +i: U32
  forall v: T
  Array<T> & T

assert Array.swap.at:
  forall -T: Type
  forall i: U32
  forall v: T
  forall an: Array<T> & U32
  Array<T> & T

assert Array.swap:
  forall -T: Type
  forall a: Array<T>
  forall +i: U32
  forall v: T
  Array<T> & T

assert Array.clone.node:
  forall cx: Array<U32> & Array<U32>
  forall cy: Array<U32> & Array<U32>
  Array<U32> & Array<U32>

assert Array.clone:
  forall a: Array<U32>
  Array<U32> & Array<U32>

assert Array.new:
  forall -T: Data
  forall +d: Nat
  forall +v: T
  Array<T>

assert Array.set.fin:
  forall -T: Type
  forall r: Array<T> & T
  Array<T>

assert Array.set:
  forall -T: Type
  forall a: Array<T>
  forall i: U32
  forall v: T
  Array<T>

assert Array.get.if:
  forall -T: Data
  forall xs: Array<T>
  forall ys: Array<T>
  forall +h: U32
  forall i: U32
  forall z: Bool
  Array<T> & T

assert Array.get.go:
  forall -T: Data
  forall a: Array<T>
  forall n: U32
  forall +i: U32
  Array<T> & T

assert Array.get.at:
  forall -T: Data
  forall i: U32
  forall an: Array<T> & U32
  Array<T> & T

assert Array.get:
  forall -T: Data
  forall a: Array<T>
  forall +i: U32
  Array<T> & T

# Map
# ---

assert Map.bit.u:
  forall x: U32
  forall k: Nat
  Bool

assert Map.bit.chr:
  forall c: Char
  forall off: Nat
  Char & Bool

assert Map.bit.go.chr:
  forall t: String
  forall r: Char & Bool
  String & Bool

assert Map.bit.go.rec:
  forall c: Char
  forall r: String & Bool
  String & Bool

assert Map.bit.go:
  forall key: String
  forall ci: Nat
  forall off: Nat
  String & Bool

assert Map.bit.at:
  forall key: String
  forall co: Nat & Nat
  String & Bool

assert Map.bit:
  forall key: String
  forall pos: Nat
  String & Bool

assert Map.msb.u.if:
  forall p: Nat
  forall x2: U32
  forall z: Bool
  Nat

assert Map.msb.u:
  forall n: Nat
  forall x: U32
  Nat

assert Map.diff.chr:
  forall x: U32
  Nat

assert Map.diff.step:
  forall x: Char
  forall y: Char
  Nat & Bool

assert Map.diff.fin:
  forall xt: String
  forall yt: String
  forall rc: Nat & Bool
  Nat

assert Map.diff:
  forall a: String
  forall b: String
  Nat

assert Map.new:
  forall -a: Quant
  forall -V: Kind(a)
  Map<a, V>

assert Map.put.bit:
  forall -a: Quant
  forall -V: Kind(a)
  forall x: V
  forall p2: Nat
  forall lo: Map<a, V>
  forall hi: Map<a, V>
  forall kb: String & Bool
  Map<a, V>

assert Map.put:
  forall -a: Quant
  forall -V: Kind(a)
  forall m: Map<a, V>
  forall key: String
  forall x: V
  Map<a, V>

assert Map.ins.splice.bit:
  forall -a: Quant
  forall -V: Kind(a)
  forall x: V
  forall rest: Map<a, V>
  forall pb: Nat
  forall kb: String & Bool
  Map<a, V>

assert Map.ins.splice:
  forall -a: Quant
  forall -V: Kind(a)
  forall +p: Nat
  forall key: String
  forall x: V
  forall rest: Map<a, V>
  Map<a, V>

assert Map.ins.deep:
  forall -a: Quant
  forall -V: Kind(a)
  forall x: V
  forall lo: Map<a, V>
  forall hi: Map<a, V>
  forall pb: Nat
  forall qb: Nat
  forall kb: String & Bool
  Map<a, V>

assert Map.ins.if:
  forall -a: Quant
  forall -V: Kind(a)
  forall key: String
  forall x: V
  forall lo: Map<a, V>
  forall hi: Map<a, V>
  forall +pos2: Nat
  forall pb: Nat
  forall t: Bool
  Map<a, V>

assert Map.ins:
  forall -a: Quant
  forall -V: Kind(a)
  forall m: Map<a, V>
  forall key: String
  forall x: V
  forall +p: Nat
  Map<a, V>

assert Map.seek.lo:
  forall -a: Quant
  forall -V: Kind(a)
  forall p2: Nat
  forall hi: Map<a, V>
  forall r0: (Map<a, V> & String) & Maybe<&2, String>
  (Map<a, V> & String) & Maybe<&2, String>

assert Map.seek.hi:
  forall -a: Quant
  forall -V: Kind(a)
  forall p2: Nat
  forall lo: Map<a, V>
  forall r0: (Map<a, V> & String) & Maybe<&2, String>
  (Map<a, V> & String) & Maybe<&2, String>

assert Map.seek.bit:
  forall -a: Quant
  forall -V: Kind(a)
  forall lo: Map<a, V>
  forall hi: Map<a, V>
  forall p2: Nat
  forall kb: String & Bool
  (Map<a, V> & String) & Maybe<&2, String>

assert Map.seek:
  forall -a: Quant
  forall -V: Kind(a)
  forall m: Map<a, V>
  forall key: String
  (Map<a, V> & String) & Maybe<&2, String>

assert Map.set.fin.go:
  forall -a: Quant
  forall -V: Kind(a)
  forall m: Map<a, V>
  forall key: String
  forall x: V
  forall r: (String & String) & Cmp
  Map<a, V>

assert Map.set.fin:
  forall -a: Quant
  forall -V: Kind(a)
  forall m: Map<a, V>
  forall key: String
  forall x: V
  forall keyb: String
  forall k: String
  Map<a, V>

assert Map.set.go:
  forall -a: Quant
  forall -V: Kind(a)
  forall x: V
  forall r: (Map<a, V> & String) & Maybe<&2, String>
  Map<a, V>

assert Map.set:
  forall -a: Quant
  forall -V: Kind(a)
  forall m: Map<a, V>
  forall key: String
  forall x: V
  Map<a, V>

assert Map.set.kv:
  forall -a: Quant
  forall -V: Kind(a)
  forall m: Map<a, V>
  forall kv: Sigma<&2, a, String, _ => V>
  Map<a, V>

assert Map.has.leaf:
  forall -a: Quant
  forall -V: Kind(a)
  forall v: V
  forall r: (String & String) & Cmp
  Map<a, V> & Bool

assert Map.has.lo:
  forall -a: Quant
  forall -V: Kind(a)
  forall p2: Nat
  forall hi: Map<a, V>
  forall r0: Map<a, V> & Bool
  Map<a, V> & Bool

assert Map.has.hi:
  forall -a: Quant
  forall -V: Kind(a)
  forall p2: Nat
  forall lo: Map<a, V>
  forall r0: Map<a, V> & Bool
  Map<a, V> & Bool

assert Map.has.bit:
  forall -a: Quant
  forall -V: Kind(a)
  forall lo: Map<a, V>
  forall hi: Map<a, V>
  forall p2: Nat
  forall kb: String & Bool
  Map<a, V> & Bool

assert Map.has:
  forall -a: Quant
  forall -V: Kind(a)
  forall m: Map<a, V>
  forall key: String
  Map<a, V> & Bool

assert Map.get.leaf:
  forall -V: Data
  forall d: V
  forall v: V
  forall r: (String & String) & Cmp
  Map<&2, V> & V

assert Map.get.lo:
  forall -V: Data
  forall p2: Nat
  forall hi: Map<&2, V>
  forall r0: Map<&2, V> & V
  Map<&2, V> & V

assert Map.get.hi:
  forall -V: Data
  forall p2: Nat
  forall lo: Map<&2, V>
  forall r0: Map<&2, V> & V
  Map<&2, V> & V

assert Map.get.bit:
  forall -V: Data
  forall d: V
  forall lo: Map<&2, V>
  forall hi: Map<&2, V>
  forall p2: Nat
  forall kb: String & Bool
  Map<&2, V> & V

assert Map.get:
  forall -V: Data
  forall d: V
  forall m: Map<&2, V>
  forall key: String
  Map<&2, V> & V

assert Map.pop.lo:
  forall -a: Quant
  forall -V: Kind(a)
  forall pos: Nat
  forall lo: Map<a, V>
  forall hi: Map<a, V>
  forall r: Maybe<a, V>
  Map<a, V> & Maybe<a, V>

assert Map.pop.hi:
  forall -a: Quant
  forall -V: Kind(a)
  forall pos: Nat
  forall lo: Map<a, V>
  forall hi: Map<a, V>
  forall r: Maybe<a, V>
  Map<a, V> & Maybe<a, V>

assert Map.pop.leaf:
  forall -a: Quant
  forall -V: Kind(a)
  forall v: V
  forall r: (String & String) & Cmp
  Map<a, V> & Maybe<a, V>

assert Map.pop.golo:
  forall -a: Quant
  forall -V: Kind(a)
  forall p2: Nat
  forall hi: Map<a, V>
  forall r0: Map<a, V> & Maybe<a, V>
  Map<a, V> & Maybe<a, V>

assert Map.pop.gohi:
  forall -a: Quant
  forall -V: Kind(a)
  forall p2: Nat
  forall lo: Map<a, V>
  forall r0: Map<a, V> & Maybe<a, V>
  Map<a, V> & Maybe<a, V>

assert Map.pop.bit:
  forall -a: Quant
  forall -V: Kind(a)
  forall lo: Map<a, V>
  forall hi: Map<a, V>
  forall p2: Nat
  forall kb: String & Bool
  Map<a, V> & Maybe<a, V>

assert Map.pop:
  forall -a: Quant
  forall -V: Kind(a)
  forall m: Map<a, V>
  forall key: String
  Map<a, V> & Maybe<a, V>

assert Map.del.fin:
  forall -a: Quant
  forall -V: Kind(a)
  forall r: Map<a, V> & Maybe<a, V>
  Map<a, V>

assert Map.del:
  forall -a: Quant
  forall -V: Kind(a)
  forall m: Map<a, V>
  forall key: String
  Map<a, V>

assert Map.to_list.go:
  forall -a: Quant
  forall -V: Kind(a)
  forall m: Map<a, V>
  forall acc: List<a, Sigma<&2, a, String, _ => V>>
  List<a, Sigma<&2, a, String, _ => V>>

assert Map.to_list:
  forall -a: Quant
  forall -V: Kind(a)
  forall m: Map<a, V>
  List<a, Sigma<&2, a, String, _ => V>>

assert Map.keys.go:
  forall -a: Quant
  forall -V: Kind(a)
  forall m: Map<a, V>
  forall acc: List<&2, String>
  List<&2, String>

assert Map.keys:
  forall -a: Quant
  forall -V: Kind(a)
  forall m: Map<a, V>
  List<&2, String>

assert Map.from_list.go:
  forall -a: Quant
  forall -V: Kind(a)
  forall kvs: List<a, Sigma<&2, a, String, _ => V>>
  forall m: Map<a, V>
  Map<a, V>

assert Map.from_list:
  forall -a: Quant
  forall -V: Kind(a)
  forall kvs: List<a, Sigma<&2, a, String, _ => V>>
  Map<a, V>

assert Map.union:
  forall -a: Quant
  forall -V: Kind(a)
  forall m: Map<a, V>
  forall n: Map<a, V>
  Map<a, V>

# Set
# ---

assert Set:
  Data

assert Set.new:
  Set()

assert Set.add:
  forall s: Set()
  forall key: String
  Set()

assert Set.has:
  forall s: Set()
  forall key: String
  Set() & Bool

assert Set.del:
  forall s: Set()
  forall key: String
  Set()

assert Set.union:
  forall a: Set()
  forall b: Set()
  Set()

# Proofs
# ======

# Word
# ----

def Word(n):
  match n:
    case 0n:
      Word.Nil
    case 1n+p:
      Word.Con<p>

# Pair
# ----

def Pair(A, B):
  Sigma<&1, &1, A, _ => B>

def Exists(A, B):
  Sigma<&1, &1, A, B>

def Or(A, B):
  Either<&1, &1, A, B>

# Effects
# -------

def IO(A):
  @-R: Type ->
  @k: (A -> IO.OP<R>) ->
  IO.OP<R>

def IO.pure(A, x):
  R => k => k(x)

def IO.bind(A, B, m, f):
  R => k => m(R, x => f(x, R, k))

def IO.print(text):
  import "./effs/print.c"
  import "./effs/print.js"

def IO.write(text):
  import "./effs/write.c"
  import "./effs/write.js"

def IO.print_err(text):
  import "./effs/print_err.c"
  import "./effs/print_err.js"

def IO.get_env(name):
  import "./effs/get_env.c"
  import "./effs/get_env.js"

def IO.die(A, code, message):
  R => k => Halt{code, message}

def IO.pass(A, r):
  match r:
    case Done{value}:
      IO.pure(A, value)
    case Fail{(code, message)}:
      IO.die(A, code, message)

def IO.try(A, action):
  IO.bind(Result<&1, &1, U32 & String, A>, A, action, IO.pass(A))

def File.open(path, mode):
  import "./effs/file_open.c"
  import "./effs/file_open.js"

def File.read(file, max):
  import "./effs/file_read.c"
  import "./effs/file_read.js"

def File.write(file, data):
  import "./effs/file_write.c"
  import "./effs/file_write.js"

def File.close(file):
  import "./effs/file_close.c"
  import "./effs/file_close.js"

def TCP.listen(port):
  import "./effs/tcp_listen.c"
  import "./effs/tcp_listen.js"

def TCP.accept(listener):
  import "./effs/tcp_accept.c"
  import "./effs/tcp_accept.js"

def TCP.connect(host, port):
  import "./effs/tcp_connect.c"
  import "./effs/tcp_connect.js"

def TCP.send(socket, data):
  import "./effs/tcp_send.c"
  import "./effs/tcp_send.js"

def TCP.recv(socket, max):
  import "./effs/tcp_recv.c"
  import "./effs/tcp_recv.js"

def UDP.bind(port):
  import "./effs/udp_bind.c"
  import "./effs/udp_bind.js"

def UDP.send_to(socket, host, port, data):
  import "./effs/udp_send_to.c"
  import "./effs/udp_send_to.js"

def UDP.recv_from(socket, max):
  import "./effs/udp_recv_from.c"
  import "./effs/udp_recv_from.js"

def Socket.close(socket):
  import "./effs/socket_close.c"
  import "./effs/socket_close.js"

def Listener.close(listener):
  import "./effs/listener_close.c"
  import "./effs/listener_close.js"

# Equal
# -----

def Equal.cong(A, B, f, a, b, e):
  %e : {f(a) == f(_) : B}; {==}

def Equal.sym(A, a, b, e):
  %e : {_ == a : A}; {==}

def Equal.trans(A, a, b, c, ab, bc):
  %bc : {a == _ : A}; ab

# Empty
# -----

def Empty.absurd(A, e):
  match e:

# Bool
# ----

def Bool.not(b):
  match b:
    case False{}:
      True{}
    case True{}:
      False{}

def Bool.and(a, b):
  match a:
    case False{}:
      False{}
    case True{}:
      b

def Bool.or(a, b):
  match a:
    case False{}:
      b
    case True{}:
      True{}

def Bool.xor(a, b):
  match a:
    case False{}:
      b
    case True{}:
      Bool.not(b)

def Bool.cmp(a, b):
  match a b:
    case False{} False{}:
      EQ{}
    case False{} True{}:
      LT{}
    case True{} False{}:
      GT{}
    case True{} True{}:
      EQ{}

def Bool.full_add(a, b, c):
  match a b c:
    case False{} False{} False{}:
      (False{}, False{})
    case False{} False{} True{}:
      (True{}, False{})
    case False{} True{} False{}:
      (True{}, False{})
    case False{} True{} True{}:
      (False{}, True{})
    case True{} False{} False{}:
      (True{}, False{})
    case True{} False{} True{}:
      (False{}, True{})
    case True{} True{} False{}:
      (False{}, True{})
    case True{} True{} True{}:
      (True{}, True{})

# Cmp
# ---

def Cmp.is_lt(c):
  match c:
    case LT{}:
      True{}
    case EQ{}:
      False{}
    case GT{}:
      False{}

def Cmp.is_eq(c):
  match c:
    case LT{}:
      False{}
    case EQ{}:
      True{}
    case GT{}:
      False{}

def Cmp.is_gt(c):
  match c:
    case LT{}:
      False{}
    case EQ{}:
      False{}
    case GT{}:
      True{}

def Cmp.is_le(c):
  match c:
    case LT{}:
      True{}
    case EQ{}:
      True{}
    case GT{}:
      False{}

def Cmp.is_ge(c):
  match c:
    case LT{}:
      False{}
    case EQ{}:
      True{}
    case GT{}:
      True{}

# Nat
# ---

def Nat.double(n):
  match n:
    case 0n:
      0n
    case 1n+p:
      2n+Nat.double(p)

def Nat.add(a, b):
  match a:
    case 0n:
      b
    case 1n+p:
      1n+Nat.add(p, b)

def Nat.sub(a, b):
  match a b:
    case 0n 0n:
      0n
    case 0n 1n+bp:
      0n
    case 1n+ap 0n:
      1n+ap
    case 1n+ap 1n+bp:
      Nat.sub(ap, bp)

def Nat.mul(a, b):
  match a:
    case 0n:
      0n
    case 1n+p:
      Nat.add(b, Nat.mul(p, b))

def Nat.divmod.go(n, m, d, r):
  match n:
    case 0n:
      (d, r)
    case 1n+np:
      match m:
        case 0n:
          Nat.divmod.go(np, r, 1n+d, 0n)
        case 1n+mp:
          Nat.divmod.go(np, mp, d, 1n+r)

def Nat.divmod(a, b):
  match b:
    case 0n:
      (0n, a)
    case 1n+bp:
      Nat.divmod.go(a, bp, 0n, 0n)

def Nat.cmp(a, b):
  match a b:
    case 0n 0n:
      EQ{}
    case 0n 1n+bp:
      LT{}
    case 1n+ap 0n:
      GT{}
    case 1n+ap 1n+bp:
      Nat.cmp(ap, bp)

def Nat.is_lt(a, b):
  Cmp.is_lt(Nat.cmp(a, b))

# Maybe
# -----

def Maybe.pure(a, A, x):
  Some{x}

def Maybe.bind(a, A, B, m, f):
  match m:
    case None{}:
      None{}
    case Some{x}:
      f(x)

# Result
# ------

def Result.pure(a, b, E, A, x):
  Done{x}

def Result.fail(a, b, E, A, e):
  Fail{e}

def Result.bind(a, b, E, A, B, r, f):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      f(x)

# Word
# ----

def Word.cast(m, n, e, w):
  %e : Word(_); w

def Word.zero(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{False{}, Word.zero(p)}

def Word.not(n, w):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{Bool.not(b), Word.not(p, t)}

def Word.and(n, a, b):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          WCon{Bool.and(ab, bb), Word.and(p, at, bt)}

def Word.or(n, a, b):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          WCon{Bool.or(ab, bb), Word.or(p, at, bt)}

def Word.xor(n, a, b):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          WCon{Bool.xor(ab, bb), Word.xor(p, at, bt)}

def Word.shl.put(n, c, w):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{c, Word.shl.put(p, b, t)}

def Word.shl(n, w):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{False{}, Word.shl.put(p, b, t)}

def Word.shl.out.con(p, c, r):
  (hi, t2) = r
  (hi, WCon{c, t2})

def Word.shl.out(n, c, w):
  match n:
    case 0n:
      (c, WNil{})
    case 1n+p:
      match w:
        case WCon{b, t}:
          Word.shl.out.con(p, c, Word.shl.out(p, b, t))

def Word.shr.pad(n, w):
  match n:
    case 0n:
      WCon{False{}, w}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{b, Word.shr.pad(p, t)}

def Word.shr(n, w):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          Word.shr.pad(p, t)

def Word.cmp.fin(ab, bb, t):
  match t:
    case LT{}:
      LT{}
    case EQ{}:
      Bool.cmp(ab, bb)
    case GT{}:
      GT{}

def Word.cmp(n, a, b):
  match n:
    case 0n:
      EQ{}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          Word.cmp.fin(ab, bb, Word.cmp(p, at, bt))

def Word.inc(n, w):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          WCon{True{}, t}
        case WCon{True{}, t}:
          WCon{False{}, Word.inc(p, t)}

def Word.adc.con(p, at, bt, f, sk):
  (s, k) = sk
  WCon{s, Word.adc(p, at, bt, f, k)}

def Word.adc(n, a, b, f, c):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match a b f:
        case WCon{ab, at} WCon{bb, bt} False{}:
          Word.adc.con(p, at, bt, False{}, Bool.full_add(ab, bb, c))
        case WCon{ab, at} WCon{bb, bt} True{}:
          Word.adc.con(p, at, bt, True{}, Bool.full_add(ab, Bool.not(bb), c))

def Word.add(n, a, b):
  Word.adc(n, a, b, False{}, False{})

def Word.sub(n, a, b):
  Word.adc(n, a, b, True{}, True{})

def Word.add_comm.arm(p, h, at, bt, k):
  Equal.cong(Word(p), Word(1n+p), w => WCon{h, w},
    Word.adc(p, at, bt, False{}, k), Word.adc(p, bt, at, False{}, k),
    Word.add_comm.go(p, at, bt, k))

def Word.add_comm.go(n, a, b, c):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, at} WCon{False{}, bt} False{}:
          Word.add_comm.arm(p, False{}, at, bt, False{})
        case WCon{False{}, at} WCon{False{}, bt} True{}:
          Word.add_comm.arm(p, True{}, at, bt, False{})
        case WCon{False{}, at} WCon{True{}, bt} False{}:
          Word.add_comm.arm(p, True{}, at, bt, False{})
        case WCon{False{}, at} WCon{True{}, bt} True{}:
          Word.add_comm.arm(p, False{}, at, bt, True{})
        case WCon{True{}, at} WCon{False{}, bt} False{}:
          Word.add_comm.arm(p, True{}, at, bt, False{})
        case WCon{True{}, at} WCon{False{}, bt} True{}:
          Word.add_comm.arm(p, False{}, at, bt, True{})
        case WCon{True{}, at} WCon{True{}, bt} False{}:
          Word.add_comm.arm(p, False{}, at, bt, True{})
        case WCon{True{}, at} WCon{True{}, bt} True{}:
          Word.add_comm.arm(p, True{}, at, bt, True{})

def Word.add_comm(n, a, b):
  Word.add_comm.go(n, a, b, False{})

def Word.to_nat(n, w):
  match n:
    case 0n:
      0n
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          Nat.double(Word.to_nat(p, t))
        case WCon{True{}, t}:
          1n+Nat.double(Word.to_nat(p, t))

def Word.mul.go(n, m, a, b, acc):
  match m:
    case 0n:
      acc
    case 1n+mp:
      match a:
        case WCon{False{}, at}:
          Word.mul.go(n, mp, at, Word.shl(n, b), acc)
        case WCon{True{}, at}:
          +b2 = b
          Word.mul.go(n, mp, at, Word.shl(n, b2), Word.add(n, acc, b2))

def Word.mul(n, a, b):
  Word.mul.go(n, n, a, b, Word.zero(n))

# U32
# ---

def U32.zero():
  U32{Word.zero(32n)}

def U32.one():
  U32{Word.inc(32n, Word.zero(32n))}

def U32.inc(a):
  match a:
    case U32{x}:
      U32{Word.inc(32n, x)}

def U32.add(a, b):
  match a b:
    case U32{x} U32{y}:
      U32{Word.add(32n, x, y)}

def U32.add_comm(a, b):
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.add(32n, x, y),
        Word.add(32n, y, x), Word.add_comm(32n, x, y))

def U32.sub(a, b):
  match a b:
    case U32{x} U32{y}:
      U32{Word.sub(32n, x, y)}

def U32.mul(a, b):
  match a b:
    case U32{x} U32{y}:
      U32{Word.mul(32n, x, y)}

def U32.not(a):
  match a:
    case U32{x}:
      U32{Word.not(32n, x)}

def U32.and(a, b):
  match a b:
    case U32{x} U32{y}:
      U32{Word.and(32n, x, y)}

def U32.or(a, b):
  match a b:
    case U32{x} U32{y}:
      U32{Word.or(32n, x, y)}

def U32.xor(a, b):
  match a b:
    case U32{x} U32{y}:
      U32{Word.xor(32n, x, y)}

def U32.shl(a):
  match a:
    case U32{x}:
      U32{Word.shl(32n, x)}

def U32.shr(a):
  match a:
    case U32{x}:
      U32{Word.shr(32n, x)}

def U32.shln(a, n):
  match n:
    case 0n:
      a
    case 1n+p:
      U32.shl(U32.shln(a, p))

def U32.shrn(a, n):
  match n:
    case 0n:
      a
    case 1n+p:
      U32.shr(U32.shrn(a, p))

def U32.cmp(a, b):
  match a b:
    case U32{x} U32{y}:
      Word.cmp(32n, x, y)

def U32.is_eq(a, b):
  Cmp.is_eq(U32.cmp(a, b))

def U32.is_ne(a, b):
  Bool.not(Cmp.is_eq(U32.cmp(a, b)))

def U32.is_lt(a, b):
  Cmp.is_lt(U32.cmp(a, b))

def U32.is_le(a, b):
  Cmp.is_le(U32.cmp(a, b))

def U32.is_gt(a, b):
  Cmp.is_gt(U32.cmp(a, b))

def U32.is_ge(a, b):
  Cmp.is_ge(U32.cmp(a, b))

def U32.is_zero(a):
  U32.is_eq(a, U32.zero())

def U32.to_nat(a):
  match a:
    case U32{w}:
      Word.to_nat(32n, w)

def U32.from_nat(n):
  match n:
    case 0n:
      U32.zero()
    case 1n+p:
      U32.inc(U32.from_nat(p))

def U32.divmod.go.fin(p, q, s, b, g):
  match g:
    case True{}:
      (WCon{True{}, q}, U32.sub(s, b))
    case False{}:
      (WCon{False{}, q}, s)

def U32.divmod.go.shl(p, q, b, ts):
  (t, s) = ts
  +s2 = {U32{s} : U32}
  U32.divmod.go.fin(p, q, s2, b, Bool.or(t, U32.is_ge(s2, b)))

def U32.divmod.go.rec(p, a0, b, qr):
  (q, r) = qr
  U32{rw} = r
  U32.divmod.go.shl(p, q, b, Word.shl.out(32n, a0, rw))

def U32.divmod.go(m, a, b):
  match m a:
    case 0n WNil{}:
      (WNil{}, U32.zero())
    case 1n+p WCon{a0, hi}:
      U32.divmod.go.rec(p, a0, b, U32.divmod.go(p, hi, b))

def U32.div.fin(qr):
  (q, r) = qr
  U32{q}

def U32.div.if(aw, b, z):
  match z:
    case True{}:
      U32.zero()
    case False{}:
      U32.div.fin(U32.divmod.go(32n, aw, b))

def U32.div(a, b):
  U32{aw} = a
  U32.div.if(aw, b, U32.is_zero(b))

def U32.mod.fin(qr):
  (q, r) = qr
  r

def U32.mod.if(aw, b, z):
  match z:
    case True{}:
      U32{aw}
    case False{}:
      U32.mod.fin(U32.divmod.go(32n, aw, b))

def U32.mod(a, b):
  U32{aw} = a
  U32.mod.if(aw, b, U32.is_zero(b))

# Char
# ----

def Char.cmp(a, b):
  match a b:
    case Chr{x} Chr{y}:
      +x2 = x
      +y2 = y
      ((Chr{x2}, Chr{y2}), U32.cmp(x2, y2))

# String
# ------

def String.append(a, b):
  match a:
    case SNil{}:
      b
    case SCon{h, t}:
      SCon{h, String.append(t, b)}

def String.cmp.rec(h1b, h2b, rr):
  ((t1b, t2b), r) = rr
  ((SCon{h1b, t1b}, SCon{h2b, t2b}), r)

def String.cmp.fin(t1, t2, hc):
  ((h1b, h2b), c) = hc
  match c:
    case LT{}:
      ((SCon{h1b, t1}, SCon{h2b, t2}), LT{})
    case EQ{}:
      String.cmp.rec(h1b, h2b, String.cmp(t1, t2))
    case GT{}:
      ((SCon{h1b, t1}, SCon{h2b, t2}), GT{})

def String.cmp(a, b):
  match a b:
    case SNil{} SNil{}:
      ((SNil{}, SNil{}), EQ{})
    case SNil{} SCon{h, t}:
      ((SNil{}, SCon{h, t}), LT{})
    case SCon{h, t} SNil{}:
      ((SCon{h, t}, SNil{}), GT{})
    case SCon{h1, t1} SCon{h2, t2}:
      String.cmp.fin(t1, t2, Char.cmp(h1, h2))

def String.eq.fin(r):
  ((a2, b2), c) = r
  Cmp.is_eq(c)

def String.eq(a, b):
  String.eq.fin(String.cmp(a, b))

# Text
# ----

def U32.read.dig.if(x, ok):
  match ok:
    case True{}:
      Some{U32.sub(x, 48)}
    case False{}:
      None{}

def U32.read.dig(c):
  match c:
    case Chr{x}:
      +x2 = x
      U32.read.dig.if(x2, Bool.and(U32.is_le(48, x2), U32.is_le(x2, 57)))

def Nat.show.put(qr):
  (q, r) = qr
  (Chr{U32.from_nat(Nat.add(48n, r))}, q)

def Nat.show.step(n):
  Nat.show.put(Nat.divmod(n, 10n))

def Nat.show.fin(g, acc, dq):
  (d, q) = dq
  match q:
    case 0n:
      SCon{d, acc}
    case 1n+p:
      Nat.show.go(g, 1n+p, SCon{d, acc})

def Nat.show.go(f, n, acc):
  match f:
    case 0n:
      acc
    case 1n+g:
      Nat.show.fin(g, acc, Nat.show.step(n))

def Nat.show(n):
  Nat.show.go(1n+n, n, SNil{})

def Nat.read.fin(t, acc, d):
  match d:
    case None{}:
      None{}
    case Some{x}:
      Nat.read.go(t, Nat.add(Nat.mul(acc, 10n), U32.to_nat(x)))

def Nat.read.go(s, acc):
  match s:
    case SNil{}:
      Some{acc}
    case SCon{h, t}:
      Nat.read.fin(t, acc, U32.read.dig(h))

def Nat.read(s):
  match s:
    case SNil{}:
      None{}
    case SCon{h, t}:
      Nat.read.go(SCon{h, t}, 0n)

def U32.show.fin(g, acc, n, z):
  match z:
    case True{}:
      acc
    case False{}:
      U32.show.go(g, U32.div(n, 10),
        SCon{Chr{U32.add(48, U32.mod(n, 10))}, acc})

def U32.show.go(f, n, acc):
  match f:
    case 0n:
      acc
    case 1n+g:
      U32.show.fin(g, acc, n, U32.is_zero(n))

def U32.show.if(a, z):
  match z:
    case True{}:
      SCon{Chr{48}, SNil{}}
    case False{}:
      U32.show.go(10n, a, SNil{})

def U32.show(a):
  U32.show.if(a, U32.is_zero(a))

def U32.read.fin(t, acc, d):
  match d:
    case None{}:
      None{}
    case Some{x}:
      U32.read.go(t, U32.add(U32.mul(acc, 10), x))

def U32.read.go(s, acc):
  match s:
    case SNil{}:
      Some{acc}
    case SCon{h, t}:
      U32.read.fin(t, acc, U32.read.dig(h))

def U32.read(s):
  match s:
    case SNil{}:
      None{}
    case SCon{h, t}:
      U32.read.go(SCon{h, t}, 0)

# Array
# -----

def Array.size.node(T, ys, r):
  (xs2, n) = r
  (ANode{xs2, ys}, U32.shl(n))

def Array.size(T, a):
  match a:
    case ALeaf{x}:
      (ALeaf{x}, 1)
    case ANode{xs, ys}:
      Array.size.node(T, ys, Array.size(T, xs))

def Array.swap.lo(T, ys, r):
  (nxs, old) = r
  (ANode{nxs, ys}, old)

def Array.swap.hi(T, xs, r):
  (nys, old) = r
  (ANode{xs, nys}, old)

def Array.swap.if(T, xs, ys, h, i, v, z):
  match z:
    case True{}:
      Array.swap.lo(T, ys, Array.swap.go(T, xs, h, i, v))
    case False{}:
      Array.swap.hi(T, xs, Array.swap.go(T, ys, h, U32.sub(i, h), v))

def Array.swap.go(T, a, n, i, v):
  match a:
    case ALeaf{x}:
      (ALeaf{v}, x)
    case ANode{xs, ys}:
      +h = U32.shr(n)
      Array.swap.if(T, xs, ys, h, i, v, U32.is_lt(i, h))

def Array.swap.at(T, i, v, an):
  (a, n) = an
  +m = n
  Array.swap.go(T, a, m, U32.and(i, U32.sub(m, 1)), v)

def Array.swap(T, a, i, v):
  Array.swap.at(T, i, v, Array.size(T, a))

def Array.clone.node(cx, cy):
  (xa, xb) = cx
  (ya, yb) = cy
  (ANode{xa, ya}, ANode{xb, yb})

def Array.clone(a):
  match a:
    case ALeaf{x}:
      +x2 = x
      (ALeaf{x2}, ALeaf{x2})
    case ANode{xs, ys}:
      Array.clone.node(Array.clone(xs), Array.clone(ys))

def Array.new(T, d, v):
  match d:
    case 0n:
      ALeaf{v}
    case 1n+p:
      ANode{Array.new(T, p, v), Array.new(T, p, v)}

def Array.set.fin(T, r):
  (na, old) = r
  na

def Array.set(T, a, i, v):
  Array.set.fin(T, Array.swap(T, a, i, v))

def Array.get.if(T, xs, ys, h, i, z):
  match z:
    case True{}:
      Array.swap.lo(T, ys, Array.get.go(T, xs, h, i))
    case False{}:
      Array.swap.hi(T, xs, Array.get.go(T, ys, h, U32.sub(i, h)))

def Array.get.go(T, a, n, i):
  match a:
    case ALeaf{x}:
      +x2 = x
      (ALeaf{x2}, x2)
    case ANode{xs, ys}:
      +h = U32.shr(n)
      Array.get.if(T, xs, ys, h, i, U32.is_lt(i, h))

def Array.get.at(T, i, an):
  (a, n) = an
  +m = n
  Array.get.go(T, a, m, U32.and(i, U32.sub(m, 1)))

def Array.get(T, a, i):
  Array.get.at(T, i, Array.size(T, a))

# Map
# ---

def Map.bit.u(x, k):
  U32.is_ne(U32.and(U32.shrn(x, k), 1), 0)

def Map.bit.chr(c, off):
  match c:
    case Chr{x}:
      match off:
        case 0n:
          (Chr{x}, True{})
        case 1n+b:
          +x2 = x
          (Chr{x2}, Map.bit.u(x2, Nat.sub(31n, b)))

def Map.bit.go.chr(t, r):
  (c2, b) = r
  (SCon{c2, t}, b)

def Map.bit.go.rec(c, r):
  (t2, b) = r
  (SCon{c, t2}, b)

def Map.bit.go(key, ci, off):
  match key:
    case SNil{}:
      (SNil{}, False{})
    case SCon{c, t}:
      match ci:
        case 0n:
          Map.bit.go.chr(t, Map.bit.chr(c, off))
        case 1n+j:
          Map.bit.go.rec(c, Map.bit.go(t, j, off))

def Map.bit.at(key, co):
  (ci, off) = co
  Map.bit.go(key, ci, off)

def Map.bit(key, pos):
  Map.bit.at(key, Nat.divmod(pos, 33n))

def Map.msb.u.if(p, x2, z):
  match z:
    case True{}:
      0n
    case False{}:
      Nat.add(1n, Map.msb.u(p, U32.shr(x2)))

def Map.msb.u(n, x):
  match n:
    case 0n:
      0n
    case 1n+p:
      +x2 = x
      Map.msb.u.if(p, x2, U32.is_zero(x2))

def Map.diff.chr(x):
  Nat.sub(33n, Map.msb.u(32n, x))

def Map.diff.step(x, y):
  match x y:
    case Chr{cx} Chr{cy}:
      +cx2 = cx
      +cy2 = cy
      (Map.diff.chr(U32.xor(cx2, cy2)), U32.is_eq(cx2, cy2))

def Map.diff.fin(xt, yt, rc):
  (r, c) = rc
  match c:
    case True{}:
      Nat.add(33n, Map.diff(xt, yt))
    case False{}:
      r

def Map.diff(a, b):
  match a b:
    case SNil{} SNil{}:
      0n
    case SNil{} SCon{h, t}:
      0n
    case SCon{h, t} SNil{}:
      0n
    case SCon{x, xt} SCon{y, yt}:
      Map.diff.fin(xt, yt, Map.diff.step(x, y))

def Map.new(a, V):
  MTip{}

def Map.put.bit(a, V, x, p2, lo, hi, kb):
  (key2, b) = kb
  match b:
    case False{}:
      MNode{p2, Map.put(a, V, lo, key2, x), hi}
    case True{}:
      MNode{p2, lo, Map.put(a, V, hi, key2, x)}

def Map.put(a, V, m, key, x):
  match m:
    case MTip{}:
      MLeaf{key, x}
    case MLeaf{k, v}:
      MLeaf{k, x}
    case MNode{pos, lo, hi}:
      +p = pos
      Map.put.bit(a, V, x, p, lo, hi, Map.bit(key, p))

def Map.ins.splice.bit(a, V, x, rest, pb, kb):
  (key2, b) = kb
  match b:
    case False{}:
      MNode{pb, MLeaf{key2, x}, rest}
    case True{}:
      MNode{pb, rest, MLeaf{key2, x}}

def Map.ins.splice(a, V, p, key, x, rest):
  Map.ins.splice.bit(a, V, x, rest, p, Map.bit(key, p))

def Map.ins.deep(a, V, x, lo, hi, pb, qb, kb):
  (key2, b) = kb
  match b:
    case False{}:
      MNode{qb, Map.ins(a, V, lo, key2, x, pb), hi}
    case True{}:
      MNode{qb, lo, Map.ins(a, V, hi, key2, x, pb)}

def Map.ins.if(a, V, key, x, lo, hi, pos2, pb, t):
  match t:
    case False{}:
      Map.ins.splice(a, V, pb, key, x, MNode{pos2, lo, hi})
    case True{}:
      Map.ins.deep(a, V, x, lo, hi, pb, pos2, Map.bit(key, pos2))

def Map.ins(a, V, m, key, x, p):
  match m:
    case MTip{}:
      MLeaf{key, x}
    case MLeaf{k, v}:
      Map.ins.splice(a, V, p, key, x, MLeaf{k, v})
    case MNode{pos, lo, hi}:
      +pos2 = pos
      Map.ins.if(a, V, key, x, lo, hi, pos2, p, Nat.is_lt(pos2, p))

def Map.seek.lo(a, V, p2, hi, r0):
  ((lo2, key3), r) = r0
  ((MNode{p2, lo2, hi}, key3), r)

def Map.seek.hi(a, V, p2, lo, r0):
  ((hi2, key3), r) = r0
  ((MNode{p2, lo, hi2}, key3), r)

def Map.seek.bit(a, V, lo, hi, p2, kb):
  (key2, b) = kb
  match b:
    case False{}:
      Map.seek.lo(a, V, p2, hi, Map.seek(a, V, lo, key2))
    case True{}:
      Map.seek.hi(a, V, p2, lo, Map.seek(a, V, hi, key2))

def Map.seek(a, V, m, key):
  match m:
    case MTip{}:
      ((MTip{}, key), None{})
    case MLeaf{k, v}:
      +k2 = k
      ((MLeaf{k2, v}, key), Some{k2})
    case MNode{pos, lo, hi}:
      +p = pos
      Map.seek.bit(a, V, lo, hi, p, Map.bit(key, p))

def Map.set.fin.go(a, V, m, key, x, r):
  ((keyb2, k2), c) = r
  match c:
    case LT{}:
      Map.ins(a, V, m, key, x, Map.diff(keyb2, k2))
    case EQ{}:
      Map.put(a, V, m, key, x)
    case GT{}:
      Map.ins(a, V, m, key, x, Map.diff(keyb2, k2))

def Map.set.fin(a, V, m, key, x, keyb, k):
  Map.set.fin.go(a, V, m, key, x, String.cmp(keyb, k))

def Map.set.go(a, V, x, r):
  ((m2, key2), found) = r
  match found:
    case None{}:
      MLeaf{key2, x}
    case Some{k}:
      +ka = {key2 : String}
      Map.set.fin(a, V, m2, ka, x, ka, k)

def Map.set(a, V, m, key, x):
  Map.set.go(a, V, x, Map.seek(a, V, m, key))

def Map.set.kv(a, V, m, kv):
  (k, v) = kv
  Map.set(a, V, m, k, v)

def Map.has.leaf(a, V, v, r):
  ((key2, k2), c) = r
  (MLeaf{k2, v}, Cmp.is_eq(c))

def Map.has.lo(a, V, p2, hi, r0):
  (lo2, r) = r0
  (MNode{p2, lo2, hi}, r)

def Map.has.hi(a, V, p2, lo, r0):
  (hi2, r) = r0
  (MNode{p2, lo, hi2}, r)

def Map.has.bit(a, V, lo, hi, p2, kb):
  (key2, b) = kb
  match b:
    case False{}:
      Map.has.lo(a, V, p2, hi, Map.has(a, V, lo, key2))
    case True{}:
      Map.has.hi(a, V, p2, lo, Map.has(a, V, hi, key2))

def Map.has(a, V, m, key):
  match m:
    case MTip{}:
      (MTip{}, False{})
    case MLeaf{k, v}:
      Map.has.leaf(a, V, v, String.cmp(key, k))
    case MNode{pos, lo, hi}:
      +p = pos
      Map.has.bit(a, V, lo, hi, p, Map.bit(key, p))

def Map.get.leaf(V, d, v, r):
  ((key2, k2), c) = r
  match c:
    case LT{}:
      (MLeaf{k2, v}, d)
    case EQ{}:
      +v2 = v
      (MLeaf{k2, v2}, v2)
    case GT{}:
      (MLeaf{k2, v}, d)

def Map.get.lo(V, p2, hi, r0):
  (lo2, r) = r0
  (MNode{p2, lo2, hi}, r)

def Map.get.hi(V, p2, lo, r0):
  (hi2, r) = r0
  (MNode{p2, lo, hi2}, r)

def Map.get.bit(V, d, lo, hi, p2, kb):
  (key2, b) = kb
  match b:
    case False{}:
      Map.get.lo(V, p2, hi, Map.get(V, d, lo, key2))
    case True{}:
      Map.get.hi(V, p2, lo, Map.get(V, d, hi, key2))

def Map.get(V, d, m, key):
  match m:
    case MTip{}:
      (MTip{}, d)
    case MLeaf{k, v}:
      Map.get.leaf(V, d, v, String.cmp(key, k))
    case MNode{pos, lo, hi}:
      +p = pos
      Map.get.bit(V, d, lo, hi, p, Map.bit(key, p))

def Map.pop.lo(a, V, pos, lo, hi, r):
  match lo:
    case MTip{}:
      (hi, r)
    case MLeaf{k, v}:
      (MNode{pos, MLeaf{k, v}, hi}, r)
    case MNode{p, a, b}:
      (MNode{pos, MNode{p, a, b}, hi}, r)

def Map.pop.hi(a, V, pos, lo, hi, r):
  match hi:
    case MTip{}:
      (lo, r)
    case MLeaf{k, v}:
      (MNode{pos, lo, MLeaf{k, v}}, r)
    case MNode{p, a, b}:
      (MNode{pos, lo, MNode{p, a, b}}, r)

def Map.pop.leaf(a, V, v, r):
  ((key2, k2), c) = r
  match c:
    case LT{}:
      (MLeaf{k2, v}, None{})
    case EQ{}:
      (MTip{}, Some{v})
    case GT{}:
      (MLeaf{k2, v}, None{})

def Map.pop.golo(a, V, p2, hi, r0):
  (lo2, r) = r0
  Map.pop.lo(a, V, p2, lo2, hi, r)

def Map.pop.gohi(a, V, p2, lo, r0):
  (hi2, r) = r0
  Map.pop.hi(a, V, p2, lo, hi2, r)

def Map.pop.bit(a, V, lo, hi, p2, kb):
  (key2, b) = kb
  match b:
    case False{}:
      Map.pop.golo(a, V, p2, hi, Map.pop(a, V, lo, key2))
    case True{}:
      Map.pop.gohi(a, V, p2, lo, Map.pop(a, V, hi, key2))

def Map.pop(a, V, m, key):
  match m:
    case MTip{}:
      (MTip{}, None{})
    case MLeaf{k, v}:
      Map.pop.leaf(a, V, v, String.cmp(key, k))
    case MNode{pos, lo, hi}:
      +p = pos
      Map.pop.bit(a, V, lo, hi, p, Map.bit(key, p))

def Map.del.fin(a, V, r):
  (m2, x) = r
  m2

def Map.del(a, V, m, key):
  Map.del.fin(a, V, Map.pop(a, V, m, key))

def Map.to_list.go(a, V, m, acc):
  match m:
    case MTip{}:
      acc
    case MLeaf{k, v}:
      Con{(k, v), acc}
    case MNode{pos, lo, hi}:
      Map.to_list.go(a, V, lo, Map.to_list.go(a, V, hi, acc))

def Map.to_list(a, V, m):
  Map.to_list.go(a, V, m, Nil{})

def Map.keys.go(a, V, m, acc):
  match m:
    case MTip{}:
      acc
    case MLeaf{k, v}:
      Con{k, acc}
    case MNode{pos, lo, hi}:
      Map.keys.go(a, V, lo, Map.keys.go(a, V, hi, acc))

def Map.keys(a, V, m):
  Map.keys.go(a, V, m, Nil{})

def Map.from_list.go(a, V, kvs, m):
  match kvs:
    case Nil{}:
      m
    case Con{kv, t}:
      Map.from_list.go(a, V, t, Map.set.kv(a, V, m, kv))

def Map.from_list(a, V, kvs):
  Map.from_list.go(a, V, kvs, MTip{})

def Map.union(a, V, m, n):
  Map.from_list.go(a, V, Map.to_list(a, V, n), m)

# Set
# ---

def Set():
  Map<&2, Unit>

def Set.new():
  Map.new(&2, Unit)

def Set.add(s, key):
  Map.set(&2, Unit, s, key, Unit{})

def Set.has(s, key):
  Map.has(&2, Unit, s, key)

def Set.del(s, key):
  Map.del(&2, Unit, s, key)

def Set.union(a, b):
  Map.union(&2, Unit, a, b)
