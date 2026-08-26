# Types
# =====

# Data
# ----

type Empty:

type Unit:
  Unit{}

type Bool:
  False{}
  True{}

type Cmp:
  LT{}
  EQ{}
  GT{}

type Either<-A: Type, -B: Type>:
  Inl{value: A}
  Inr{value: B}

type Sigma<-A: Type, -B: @-x: A -> Type>:
  Tuple{fst: A, snd: B(fst)}

type Nat:
  Zero{}
  Succ{pred: Nat}

type Maybe<-A: Type>:
  None{}
  Some{value: A}

type Result<-E: Type, -A: Type>:
  Fail{error: E}
  Done{value: A}

type List<-A: Type>:
  Nil{}
  Con{head: A, tail: List<A>}

type Array<-T: Type>:
  ALeaf{value: T}
  ANode{xs: Array<T>, ys: Array<T>}

assert Word:
  forall n: Nat
  Type

type Word.Nil:
  WNil{}

type Word.Con<-p: Nat>:
  WCon{head: Bool, tail: Word(p)}

type U32:
  U32{data: Word(32n)}

type Char:
  Chr{code: U32}

type String:
  SNil{}
  SCon{head: Char, tail: String}

# Effects
# -------

type File:
  File{slot: U32, gen: U32}

type Socket:
  Socket{slot: U32, gen: U32}

type Listener:
  Listener{slot: U32, gen: U32}

type IO.OP<-R: Type>:
  Emit{value: R}
  Halt{code: U32, message: String}

# Map
# ---

type Map<-V: Type>:
  MTip{}
  MLeaf{key: String, val: V}
  MNode{pos: Nat, lo: Map<V>, hi: Map<V>}

# Claims
# ======

# Pair
# ----

assert Pair:
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
  IO(Result<(U32 & String), String>)

assert IO.die:
  forall -A: Type
  forall code: U32
  forall message: String
  IO(A)

assert IO.pass:
  forall -A: Type
  forall r: Result<(U32 & String), A>
  IO(A)

assert IO.try:
  forall -A: Type
  forall action: IO(Result<(U32 & String), A>)
  IO(A)

assert File.open:
  forall path: String
  forall mode: String
  IO(Result<(U32 & String), File>)

assert File.read:
  forall file: File
  forall max: U32
  IO(File & Result<(U32 & String), String>)

assert File.write:
  forall file: File
  forall data: String
  IO(File & Result<(U32 & String), Unit>)

assert File.close:
  forall file: File
  IO(Unit)

assert TCP.listen:
  forall port: U32
  IO(Result<(U32 & String), Listener>)

assert TCP.accept:
  forall listener: Listener
  IO(Listener & Result<(U32 & String), Socket>)

assert TCP.connect:
  forall host: String
  forall port: U32
  IO(Result<(U32 & String), Socket>)

assert TCP.send:
  forall socket: Socket
  forall data: String
  IO(Socket & Result<(U32 & String), Unit>)

assert TCP.recv:
  forall socket: Socket
  forall max: U32
  IO(Socket & Result<(U32 & String), String>)

assert UDP.bind:
  forall port: U32
  IO(Result<(U32 & String), Socket>)

assert UDP.send_to:
  forall socket: Socket
  forall host: String
  forall port: U32
  forall data: String
  IO(Socket & Result<(U32 & String), Unit>)

assert UDP.recv_from:
  forall socket: Socket
  forall max: U32
  IO(Socket & Result<(U32 & String), String & U32 & String>)

assert Socket.close:
  forall socket: Socket
  IO(Unit)

assert Listener.close:
  forall listener: Listener
  IO(Unit)

# Copy
# ----

assert Copy:
  forall -A: Type
  forall -x: A
  Type

assert Copiable:
  forall -T: Type
  Type

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

assert Equal.copy:
  forall -A: Type
  forall -a: A
  forall -b: A
  forall e: {a == b : A}
  Copy({a == b : A}, e) & Copy({a == b : A}, e)

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

assert Bool.copy:
  forall b: Bool
  Copy(Bool, b) & Copy(Bool, b)

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

assert Nat.copy.succ:
  forall -p: Nat
  forall c: Copy(Nat, p) & Copy(Nat, p)
  Copy(Nat, 1n+p) & Copy(Nat, 1n+p)

assert Nat.copy:
  forall n: Nat
  Copy(Nat, n) & Copy(Nat, n)

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

assert Nat.mul.succ:
  forall -b: Nat
  forall p: Nat
  forall c: Copy(Nat, b) & Copy(Nat, b)
  Nat

assert Nat.mul:
  forall a: Nat
  forall b: Nat
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
  forall -A: Type
  forall x: A
  Maybe<A>

assert Maybe.bind:
  forall -A: Type
  forall -B: Type
  forall m: Maybe<A>
  forall f: A -> Maybe<B>
  Maybe<B>

# Result
# ------

assert Result.pure:
  forall -E: Type
  forall -A: Type
  forall x: A
  Result<E, A>

assert Result.fail:
  forall -E: Type
  forall -A: Type
  forall e: E
  Result<E, A>

assert Result.bind:
  forall -E: Type
  forall -A: Type
  forall -B: Type
  forall r: Result<E, A>
  forall f: A -> Result<E, B>
  Result<E, B>

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

assert Word.copy.con:
  forall -p: Nat
  forall -rest: Word(p)
  forall b: Bool
  forall c: Copy(Word(p), rest) & Copy(Word(p), rest)
  Copy(Word.Con<p>, WCon{b, rest}) & Copy(Word.Con<p>, WCon{b, rest})

assert Word.copy:
  forall n: Nat
  forall w: Word(n)
  Copy(Word(n), w) & Copy(Word(n), w)

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

assert Word.mul.step.fin:
  forall -ip: Nat
  forall bb2: Bool
  forall o: Bool
  forall w: (&r: Nat -> {ip == r : Nat} & Word(r) & Word(r))
  exists r: Nat
  {1n+ip == r : Nat} & Word(r) & Word(r)

assert Word.mul.step.add:
  forall ip: Nat
  forall bt: Word(ip)
  forall qb: Bool
  forall qt: Word(ip)
  forall bb2: Bool
  forall a02: Bool
  forall ok: Bool & Bool
  exists r: Nat
  {1n+ip == r : Nat} & Word(r) & Word(r)

assert Word.mul.step.con:
  forall ip: Nat
  forall s: Bool
  forall c: Bool
  forall bt: Word(ip)
  forall qb: Bool
  forall qt: Word(ip)
  forall -bb: Bool
  forall -a0: Bool
  forall cb: Copy(Bool, bb) & Copy(Bool, bb)
  forall ca: Copy(Bool, a0) & Copy(Bool, a0)
  exists r: Nat
  {1n+ip == r : Nat} & Word(r) & Word(r)

assert Word.mul.step:
  forall i: Nat
  forall a0: Bool
  forall s: Bool
  forall c: Bool
  forall b: Word(i)
  forall q: Word(i)
  exists r: Nat
  {i == r : Nat} & Word(r) & Word(r)

assert Word.mul.go.zero.b:
  forall -i: Nat
  forall b: Word(i)
  forall i1: Nat
  forall i2: Nat
  forall f1a: {i == i1 : Nat}
  forall -f1b: {i == i1 : Nat}
  forall f2: {i == i2 : Nat}
  forall cf: Copy({i == i1 : Nat}, f1b) & Copy({i == i1 : Nat}, f1b)
  exists r: Nat
  {i == r : Nat} & Word(r) & Word(r)

assert Word.mul.go.zero.a:
  forall -i: Nat
  forall b: Word(i)
  forall i1: Nat
  forall i2: Nat
  forall -f1: {i == i1 : Nat}
  forall f2: {i == i2 : Nat}
  forall cf: Copy({i == i1 : Nat}, f1) & Copy({i == i1 : Nat}, f1)
  exists r: Nat
  {i == r : Nat} & Word(r) & Word(r)

assert Word.mul.go.zero:
  forall -i: Nat
  forall b: Word(i)
  forall ci: Copy(Nat, i) & Copy(Nat, i)
  exists r: Nat
  {i == r : Nat} & Word(r) & Word(r)

assert Word.mul.go.succ.a:
  forall -i: Nat
  forall -r1: Nat
  forall g1: {i == r1 : Nat}
  forall w: (&r: Nat -> {r1 == r : Nat} & Word(r) & Word(r))
  exists r: Nat
  {i == r : Nat} & Word(r) & Word(r)

assert Word.mul.go.succ:
  forall -i: Nat
  forall a0: Bool
  forall w: (&r: Nat -> {i == r : Nat} & Word(r) & Word(r))
  exists r: Nat
  {i == r : Nat} & Word(r) & Word(r)

assert Word.mul.go:
  forall m: Nat
  forall a: Word(m)
  forall i: Nat
  forall b: Word(i)
  exists r: Nat
  {i == r : Nat} & Word(r) & Word(r)

assert Word.mul.run.b:
  forall -n: Nat
  forall -n2: Nat
  forall e2b: {n == n2 : Nat}
  forall w: (&r: Nat -> {n2 == r : Nat} & Word(r) & Word(r))
  Word(n)

assert Word.mul.run.a:
  forall -n: Nat
  forall a: Word(n)
  forall b: Word(n)
  forall n1: Nat
  forall n2: Nat
  forall e1: {n == n1 : Nat}
  forall -e2: {n == n2 : Nat}
  forall ce: Copy({n == n2 : Nat}, e2) & Copy({n == n2 : Nat}, e2)
  Word(n)

assert Word.mul.run:
  forall -n: Nat
  forall a: Word(n)
  forall b: Word(n)
  forall cn: Copy(Nat, n) & Copy(Nat, n)
  Word(n)

assert Word.mul:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  Word(n)

# U32
# ---

assert U32.zero:
  U32

assert U32.one:
  U32

assert U32.copy.go:
  forall -w: Word(32n)
  forall c: Copy(Word(32n), w) & Copy(Word(32n), w)
  Copy(U32, U32{w}) & Copy(U32, U32{w})

assert U32.copy:
  forall u: U32
  Copy(U32, u) & Copy(U32, u)

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
  forall n: Nat
  forall a: U32
  U32

assert U32.shrn:
  forall n: Nat
  forall a: U32
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
  forall s2: Word(32n)
  forall b4: U32
  forall g: Bool
  Word(1n+p) & U32

assert U32.divmod.go.cpy:
  forall -p: Nat
  forall q: Word(p)
  forall t: Bool
  forall b3: U32
  forall b4: U32
  forall -s: Word(32n)
  forall cs: Copy(Word(32n), s) & Copy(Word(32n), s)
  Word(1n+p) & U32

assert U32.divmod.go.shl:
  forall -p: Nat
  forall q: Word(p)
  forall -b2: U32
  forall cb2: Copy(U32, b2) & Copy(U32, b2)
  forall ts: Bool & Word(32n)
  Word(1n+p) & U32

assert U32.divmod.go.rec:
  forall -p: Nat
  forall a0: Bool
  forall b2: U32
  forall qr: Word(p) & U32
  Word(1n+p) & U32

assert U32.divmod.go.con:
  forall -b: U32
  forall p: Nat
  forall a0: Bool
  forall hi: Word(p)
  forall cb: Copy(U32, b) & Copy(U32, b)
  Word(1n+p) & U32

assert U32.divmod.go:
  forall m: Nat
  forall a: Word(m)
  forall b: U32
  Word(m) & U32

assert U32.div.fin:
  forall qr: Word(32n) & U32
  U32

assert U32.div.if:
  forall aw: Word(32n)
  forall b2: U32
  forall z: Bool
  U32

assert U32.div.cpy:
  forall aw: Word(32n)
  forall -b: U32
  forall cb: Copy(U32, b) & Copy(U32, b)
  U32

assert U32.div:
  forall a: U32
  forall b: U32
  U32

assert U32.mod.fin:
  forall qr: Word(32n) & U32
  U32

assert U32.mod.if:
  forall aw: Word(32n)
  forall b2: U32
  forall z: Bool
  U32

assert U32.mod.cpy:
  forall aw: Word(32n)
  forall -b: U32
  forall cb: Copy(U32, b) & Copy(U32, b)
  U32

assert U32.mod:
  forall a: U32
  forall b: U32
  U32

# F32
# ---

assert F32:
  Type

assert U32.to_f32:
  forall a: U32
  F32

assert F32.to_u32:
  forall a: F32
  U32

assert F32.copy:
  forall a: F32
  Copy(F32, a) & Copy(F32, a)

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

assert F32.sqrt:
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

assert F32.make:
  forall m: U32
  forall s: U32
  F32

# Char
# ----

assert Char.copy.go:
  forall -x: U32
  forall c: Copy(U32, x) & Copy(U32, x)
  Char & Char

assert Char.copy:
  forall c: Char
  Char & Char

assert Char.cmp.go:
  forall -x: U32
  forall -y: U32
  forall cx: Copy(U32, x) & Copy(U32, x)
  forall cy: Copy(U32, y) & Copy(U32, y)
  (Char & Char) & Cmp

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

assert String.copy.con:
  forall hh: Char & Char
  forall tt: String & String
  String & String

assert String.copy:
  forall s: String
  String & String

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
  forall x4: U32
  forall ok: Bool
  Maybe<U32>

assert U32.read.dig.cpy:
  forall x1: U32
  forall -x2: U32
  forall c2: Copy(U32, x2) & Copy(U32, x2)
  Maybe<U32>

assert U32.read.dig.go:
  forall -x: U32
  forall c: Copy(U32, x) & Copy(U32, x)
  Maybe<U32>

assert U32.read.dig:
  forall c: Char
  Maybe<U32>

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

assert Nat.show.run:
  forall -n: Nat
  forall c: Copy(Nat, n) & Copy(Nat, n)
  String

assert Nat.show:
  forall n: Nat
  String

assert Nat.read.fin:
  forall t: String
  forall acc: Nat
  forall d: Maybe<U32>
  Maybe<Nat>

assert Nat.read.go:
  forall s: String
  forall acc: Nat
  Maybe<Nat>

assert Nat.read:
  forall s: String
  Maybe<Nat>

assert U32.show.fin:
  forall g: Nat
  forall acc: String
  forall n3: U32
  forall n4: U32
  forall z: Bool
  String

assert U32.show.cpy:
  forall g: Nat
  forall acc: String
  forall n1: U32
  forall -n2: U32
  forall c2: Copy(U32, n2) & Copy(U32, n2)
  String

assert U32.show.con:
  forall g: Nat
  forall acc: String
  forall -n: U32
  forall c: Copy(U32, n) & Copy(U32, n)
  String

assert U32.show.go:
  forall f: Nat
  forall n: U32
  forall acc: String
  String

assert U32.show.if:
  forall a2: U32
  forall z: Bool
  String

assert U32.show.run:
  forall -a: U32
  forall c: Copy(U32, a) & Copy(U32, a)
  String

assert U32.show:
  forall a: U32
  String

assert U32.read.fin:
  forall t: String
  forall acc: U32
  forall d: Maybe<U32>
  Maybe<U32>

assert U32.read.go:
  forall s: String
  forall acc: U32
  Maybe<U32>

assert U32.read:
  forall s: String
  Maybe<U32>

# Array
# -----

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
  forall i2: U32
  forall v: T
  forall z: Bool
  Array<T> & T

assert Array.swap.node:
  forall -T: Type
  forall xs: Array<T>
  forall ys: Array<T>
  forall v: T
  forall -i: U32
  forall ci: Copy(U32, i) & Copy(U32, i)
  Array<T> & T

assert Array.swap:
  forall -T: Type
  forall a: Array<T>
  forall i: U32
  forall v: T
  Array<T> & T

assert Array.copy.leaf:
  forall -x: U32
  forall c: Copy(U32, x) & Copy(U32, x)
  Array<U32> & Array<U32>

assert Array.copy.node:
  forall cx: Array<U32> & Array<U32>
  forall cy: Array<U32> & Array<U32>
  Array<U32> & Array<U32>

assert Array.copy:
  forall a: Array<U32>
  Array<U32> & Array<U32>

assert Array.new.node:
  forall lr: Array<U32> & Array<U32>
  Array<U32>

assert Array.new:
  forall d: Nat
  forall v: U32
  Array<U32>

assert Array.set.fin:
  forall r: Array<U32> & U32
  Array<U32>

assert Array.set:
  forall a: Array<U32>
  forall i: U32
  forall v: U32
  Array<U32>

assert Array.get.leaf:
  forall -x: U32
  forall c: Copy(U32, x) & Copy(U32, x)
  Array<U32> & U32

assert Array.get.lo:
  forall ys: Array<U32>
  forall r: Array<U32> & U32
  Array<U32> & U32

assert Array.get.hi:
  forall xs: Array<U32>
  forall r: Array<U32> & U32
  Array<U32> & U32

assert Array.get.if:
  forall xs: Array<U32>
  forall ys: Array<U32>
  forall i2: U32
  forall z: Bool
  Array<U32> & U32

assert Array.get.node:
  forall xs: Array<U32>
  forall ys: Array<U32>
  forall -i: U32
  forall ci: Copy(U32, i) & Copy(U32, i)
  Array<U32> & U32

assert Array.get:
  forall a: Array<U32>
  forall i: U32
  Array<U32> & U32

# Map
# ---

assert Map.bit.u:
  forall x: U32
  forall k: Nat
  Bool

assert Map.bit.chr.go:
  forall b: Nat
  forall -x: U32
  forall c: Copy(U32, x) & Copy(U32, x)
  Char & Bool

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

assert Map.msb.u.go:
  forall p: Nat
  forall -x: U32
  forall c: Copy(U32, x) & Copy(U32, x)
  Nat

assert Map.msb.u:
  forall n: Nat
  forall x: U32
  Nat

assert Map.diff.chr:
  forall x: U32
  Nat

assert Map.diff.step.go:
  forall -cx: U32
  forall -cy: U32
  forall ax: Copy(U32, cx) & Copy(U32, cx)
  forall ay: Copy(U32, cy) & Copy(U32, cy)
  Nat & Bool

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
  forall -V: Type
  Map<V>

assert Map.put.bit:
  forall -V: Type
  forall x: V
  forall p2: Nat
  forall lo: Map<V>
  forall hi: Map<V>
  forall kb: String & Bool
  Map<V>

assert Map.put.node:
  forall -V: Type
  forall key: String
  forall x: V
  forall lo: Map<V>
  forall hi: Map<V>
  forall -pos: Nat
  forall cq: Copy(Nat, pos) & Copy(Nat, pos)
  Map<V>

assert Map.put:
  forall -V: Type
  forall m: Map<V>
  forall key: String
  forall x: V
  Map<V>

assert Map.ins.splice.bit:
  forall -V: Type
  forall x: V
  forall rest: Map<V>
  forall pb: Nat
  forall kb: String & Bool
  Map<V>

assert Map.ins.splice.cpy:
  forall -V: Type
  forall key: String
  forall x: V
  forall rest: Map<V>
  forall -p: Nat
  forall cq: Copy(Nat, p) & Copy(Nat, p)
  Map<V>

assert Map.ins.splice:
  forall -V: Type
  forall p: Nat
  forall key: String
  forall x: V
  forall rest: Map<V>
  Map<V>

assert Map.ins.deep:
  forall -V: Type
  forall x: V
  forall lo: Map<V>
  forall hi: Map<V>
  forall pb: Nat
  forall qb: Nat
  forall kb: String & Bool
  Map<V>

assert Map.ins.down:
  forall -V: Type
  forall key: String
  forall x: V
  forall lo: Map<V>
  forall hi: Map<V>
  forall pb: Nat
  forall -pos2: Nat
  forall cq: Copy(Nat, pos2) & Copy(Nat, pos2)
  Map<V>

assert Map.ins.if:
  forall -V: Type
  forall key: String
  forall x: V
  forall lo: Map<V>
  forall hi: Map<V>
  forall pos2: Nat
  forall pb: Nat
  forall t: Bool
  Map<V>

assert Map.ins.node:
  forall -V: Type
  forall key: String
  forall x: V
  forall lo: Map<V>
  forall hi: Map<V>
  forall -pos: Nat
  forall -p: Nat
  forall cpos: Copy(Nat, pos) & Copy(Nat, pos)
  forall cp2: Copy(Nat, p) & Copy(Nat, p)
  Map<V>

assert Map.ins:
  forall -V: Type
  forall m: Map<V>
  forall key: String
  forall x: V
  forall p: Nat
  Map<V>

assert Map.seek.leaf:
  forall -V: Type
  forall v: V
  forall key: String
  forall kk: String & String
  (Map<V> & String) & Maybe<String>

assert Map.seek.lo:
  forall -V: Type
  forall p2: Nat
  forall hi: Map<V>
  forall r0: (Map<V> & String) & Maybe<String>
  (Map<V> & String) & Maybe<String>

assert Map.seek.hi:
  forall -V: Type
  forall p2: Nat
  forall lo: Map<V>
  forall r0: (Map<V> & String) & Maybe<String>
  (Map<V> & String) & Maybe<String>

assert Map.seek.bit:
  forall -V: Type
  forall lo: Map<V>
  forall hi: Map<V>
  forall p2: Nat
  forall kb: String & Bool
  (Map<V> & String) & Maybe<String>

assert Map.seek.node:
  forall -V: Type
  forall key: String
  forall lo: Map<V>
  forall hi: Map<V>
  forall -pos: Nat
  forall cq: Copy(Nat, pos) & Copy(Nat, pos)
  (Map<V> & String) & Maybe<String>

assert Map.seek:
  forall -V: Type
  forall m: Map<V>
  forall key: String
  (Map<V> & String) & Maybe<String>

assert Map.set.fin.go:
  forall -V: Type
  forall m: Map<V>
  forall key: String
  forall x: V
  forall r: (String & String) & Cmp
  Map<V>

assert Map.set.fin:
  forall -V: Type
  forall m: Map<V>
  forall key: String
  forall x: V
  forall keyb: String
  forall k: String
  Map<V>

assert Map.set.some:
  forall -V: Type
  forall m2: Map<V>
  forall x: V
  forall k: String
  forall kk: String & String
  Map<V>

assert Map.set.go:
  forall -V: Type
  forall x: V
  forall r: (Map<V> & String) & Maybe<String>
  Map<V>

assert Map.set:
  forall -V: Type
  forall m: Map<V>
  forall key: String
  forall x: V
  Map<V>

assert Map.set.kv:
  forall -V: Type
  forall m: Map<V>
  forall kv: String & V
  Map<V>

assert Map.has.leaf:
  forall -V: Type
  forall v: V
  forall r: (String & String) & Cmp
  Map<V> & Bool

assert Map.has.lo:
  forall -V: Type
  forall p2: Nat
  forall hi: Map<V>
  forall r0: Map<V> & Bool
  Map<V> & Bool

assert Map.has.hi:
  forall -V: Type
  forall p2: Nat
  forall lo: Map<V>
  forall r0: Map<V> & Bool
  Map<V> & Bool

assert Map.has.bit:
  forall -V: Type
  forall lo: Map<V>
  forall hi: Map<V>
  forall p2: Nat
  forall kb: String & Bool
  Map<V> & Bool

assert Map.has.node:
  forall -V: Type
  forall key: String
  forall lo: Map<V>
  forall hi: Map<V>
  forall -pos: Nat
  forall cq: Copy(Nat, pos) & Copy(Nat, pos)
  Map<V> & Bool

assert Map.has:
  forall -V: Type
  forall m: Map<V>
  forall key: String
  Map<V> & Bool

assert Map.get.eq:
  forall -V: Type
  forall k2: String
  forall vv: V & V
  Map<V> & V

assert Map.get.leaf:
  forall -V: Type
  forall cp: V -> (V & V)
  forall d: V
  forall v: V
  forall r: (String & String) & Cmp
  Map<V> & V

assert Map.get.lo:
  forall -V: Type
  forall p2: Nat
  forall hi: Map<V>
  forall r0: Map<V> & V
  Map<V> & V

assert Map.get.hi:
  forall -V: Type
  forall p2: Nat
  forall lo: Map<V>
  forall r0: Map<V> & V
  Map<V> & V

assert Map.get.bit:
  forall -V: Type
  forall cp: V -> (V & V)
  forall d: V
  forall lo: Map<V>
  forall hi: Map<V>
  forall p2: Nat
  forall kb: String & Bool
  Map<V> & V

assert Map.get.node:
  forall -V: Type
  forall cp: V -> (V & V)
  forall d: V
  forall key: String
  forall lo: Map<V>
  forall hi: Map<V>
  forall -pos: Nat
  forall cq: Copy(Nat, pos) & Copy(Nat, pos)
  Map<V> & V

assert Map.get:
  forall -V: Type
  forall cp: V -> (V & V)
  forall d: V
  forall m: Map<V>
  forall key: String
  Map<V> & V

assert Map.pop.lo:
  forall -V: Type
  forall pos: Nat
  forall lo: Map<V>
  forall hi: Map<V>
  forall r: Maybe<V>
  Map<V> & Maybe<V>

assert Map.pop.hi:
  forall -V: Type
  forall pos: Nat
  forall lo: Map<V>
  forall hi: Map<V>
  forall r: Maybe<V>
  Map<V> & Maybe<V>

assert Map.pop.leaf:
  forall -V: Type
  forall v: V
  forall r: (String & String) & Cmp
  Map<V> & Maybe<V>

assert Map.pop.golo:
  forall -V: Type
  forall p2: Nat
  forall hi: Map<V>
  forall r0: Map<V> & Maybe<V>
  Map<V> & Maybe<V>

assert Map.pop.gohi:
  forall -V: Type
  forall p2: Nat
  forall lo: Map<V>
  forall r0: Map<V> & Maybe<V>
  Map<V> & Maybe<V>

assert Map.pop.bit:
  forall -V: Type
  forall lo: Map<V>
  forall hi: Map<V>
  forall p2: Nat
  forall kb: String & Bool
  Map<V> & Maybe<V>

assert Map.pop.node:
  forall -V: Type
  forall key: String
  forall lo: Map<V>
  forall hi: Map<V>
  forall -pos: Nat
  forall cq: Copy(Nat, pos) & Copy(Nat, pos)
  Map<V> & Maybe<V>

assert Map.pop:
  forall -V: Type
  forall m: Map<V>
  forall key: String
  Map<V> & Maybe<V>

assert Map.del.fin:
  forall -V: Type
  forall r: Map<V> & Maybe<V>
  Map<V>

assert Map.del:
  forall -V: Type
  forall m: Map<V>
  forall key: String
  Map<V>

assert Map.to_list.go:
  forall -V: Type
  forall m: Map<V>
  forall acc: List<(String & V)>
  List<(String & V)>

assert Map.to_list:
  forall -V: Type
  forall m: Map<V>
  List<(String & V)>

assert Map.keys.go:
  forall -V: Type
  forall m: Map<V>
  forall acc: List<String>
  List<String>

assert Map.keys:
  forall -V: Type
  forall m: Map<V>
  List<String>

assert Map.from_list.go:
  forall -V: Type
  forall kvs: List<(String & V)>
  forall m: Map<V>
  Map<V>

assert Map.from_list:
  forall -V: Type
  forall kvs: List<(String & V)>
  Map<V>

assert Map.union:
  forall -V: Type
  forall a: Map<V>
  forall b: Map<V>
  Map<V>

# Set
# ---

assert Set:
  Type

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
  Sigma<A, _ => B>

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
  IO.bind(Result<(U32 & String), A>, A, action, IO.pass(A))

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

# Copy
# ----

def Copy(A, x):
  &y: A -> {x == y : A}

def Copiable(T):
  @x: T -> Copy(T, x) & Copy(T, x)

# Equal
# -----

def Equal.cong(A, B, f, a, b, e):
  %e : {f(a) == f(_) : B}; {==}

def Equal.sym(A, a, b, e):
  %e : {_ == a : A}; {==}

def Equal.trans(A, a, b, c, ab, bc):
  %bc : {a == _ : A}; ab

def Equal.copy(A, a, b, e):
  %x@e : Copy({a == _ : A}, x) & Copy({a == _ : A}, x);
  (({==}, {==}), ({==}, {==}))

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

def Bool.copy(b):
  match b:
    case False{}:
      ((False{}, {==}), (False{}, {==}))
    case True{}:
      ((True{}, {==}), (True{}, {==}))

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

def Nat.copy.succ(p, c):
  ((a, ea), (b, eb)) = c
  pa = Equal.cong(Nat, Nat, x => 1n+x, p, a, ea)
  pb = Equal.cong(Nat, Nat, x => 1n+x, p, b, eb)
  ((1n+a, pa), (1n+b, pb))

def Nat.copy(n):
  match n:
    case 0n:
      ((0n, {==}), (0n, {==}))
    case 1n+p:
      Nat.copy.succ(p, Nat.copy(p))

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

def Nat.mul.succ(b, p, c):
  ((b1, e1), (b2, e2)) = c
  Nat.add(b1, Nat.mul(p, b2))

def Nat.mul(a, b):
  match a:
    case 0n:
      0n
    case 1n+p:
      Nat.mul.succ(b, p, Nat.copy(b))

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

def Maybe.pure(A, x):
  Some{x}

def Maybe.bind(A, B, m, f):
  match m:
    case None{}:
      None{}
    case Some{x}:
      f(x)

# Result
# ------

def Result.pure(E, A, x):
  Done{x}

def Result.fail(E, A, e):
  Fail{e}

def Result.bind(E, A, B, r, f):
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

def Word.copy.con(p, rest, b, c):
  match b:
    case False{}:
      ((r1, e1), (r2, e2)) = c
      pa = Equal.cong(Word(p), Word(1n+p), y => WCon{False{}, y},
        rest, r1, e1)
      pb = Equal.cong(Word(p), Word(1n+p), y => WCon{False{}, y},
        rest, r2, e2)
      ((WCon{False{}, r1}, pa), (WCon{False{}, r2}, pb))
    case True{}:
      ((r1, e1), (r2, e2)) = c
      pa = Equal.cong(Word(p), Word(1n+p), y => WCon{True{}, y},
        rest, r1, e1)
      pb = Equal.cong(Word(p), Word(1n+p), y => WCon{True{}, y},
        rest, r2, e2)
      ((WCon{True{}, r1}, pa), (WCon{True{}, r2}, pb))

def Word.copy(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          ((WNil{}, {==}), (WNil{}, {==}))
    case 1n+p:
      match w:
        case WCon{b, rest}:
          Word.copy.con(p, rest, b, Word.copy(p, rest))

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

def Word.mul.step.fin(ip, bb2, o, w):
  (r, er, be, rt) = w
  ce = Equal.cong(Nat, Nat, x => 1n+x, ip, r, er)
  (1n+r, ce, WCon{bb2, be}, WCon{o, rt})

def Word.mul.step.add(ip, bt, qb, qt, bb2, a02, ok):
  (o, k) = ok
  Word.mul.step.fin(ip, bb2, o, Word.mul.step(ip, a02, qb, k, bt, qt))

def Word.mul.step.con(ip, s, c, bt, qb, qt, bb, a0, cb, ca):
  ((bb1, x1), (bb2, x2)) = cb
  ((a01, y1), (a02, y2)) = ca
  Word.mul.step.add(ip, bt, qb, qt, bb2, a02,
    Bool.full_add(Bool.and(a01, bb1), s, c))

def Word.mul.step(i, a0, s, c, b, q):
  match i:
    case 0n:
      match b q:
        case WNil{} WNil{}:
          (0n, {==}, WNil{}, WNil{})
    case 1n+ip:
      match b q:
        case WCon{bb, bt} WCon{qb, qt}:
          Word.mul.step.con(ip, s, c, bt, qb, qt, bb, a0,
            Bool.copy(bb), Bool.copy(a0))

def Word.mul.go.zero.b(i, b, i1, i2, f1a, f1b, f2, cf):
  ((f1c, u3), (f1d, u4)) = cf
  z = Word.cast(i2, i1, Equal.trans(Nat, i2, i, i1,
    Equal.sym(Nat, i, i2, f2), f1c), Word.zero(i2))
  (i1, f1a, Word.cast(i, i1, f1d, b), z)

def Word.mul.go.zero.a(i, b, i1, i2, f1, f2, cf):
  ((f1a, u1), (f1b, u2)) = cf
  Word.mul.go.zero.b(i, b, i1, i2, f1a, f1b, f2,
    Equal.copy(Nat, i, i1, f1b))

def Word.mul.go.zero(i, b, ci):
  ((i1, f1), (i2, f2)) = ci
  Word.mul.go.zero.a(i, b, i1, i2, f1, f2, Equal.copy(Nat, i, i1, f1))

def Word.mul.go.succ.a(i, r1, g1, w):
  (r2, g2, w2, p) = w
  (r2, Equal.trans(Nat, i, r1, r2, g1, g2), w2, p)

def Word.mul.go.succ(i, a0, w):
  (r1, g1, w1, q) = w
  Word.mul.go.succ.a(i, r1, g1,
    Word.mul.step(r1, a0, False{}, False{}, w1, q))

def Word.mul.go(m, a, i, b):
  match m a:
    case 0n WNil{}:
      Word.mul.go.zero(i, b, Nat.copy(i))
    case 1n+mp WCon{a0, at}:
      Word.mul.go.succ(i, a0, Word.mul.go(mp, at, i, b))

def Word.mul.run.b(n, n2, e2b, w):
  (r, g, wr, p) = w
  %Equal.sym(Nat, n, r, Equal.trans(Nat, n, n2, r, e2b, g)) : Word(_); p

def Word.mul.run.a(n, a, b, n1, n2, e1, e2, ce):
  ((e2a, u1), (e2b, u2)) = ce
  Word.mul.run.b(n, n2, e2b, Word.mul.go(n1, Word.cast(n, n1, e1, a), n2,
    Word.cast(n, n2, e2a, b)))

def Word.mul.run(n, a, b, cn):
  ((n1, e1), (n2, e2)) = cn
  Word.mul.run.a(n, a, b, n1, n2, e1, e2, Equal.copy(Nat, n, n2, e2))

def Word.mul(n, a, b):
  Word.mul.run(n, a, b, Nat.copy(n))

# U32
# ---

def U32.zero():
  U32{Word.zero(32n)}

def U32.one():
  U32{Word.inc(32n, Word.zero(32n))}

def U32.copy.go(w, c):
  ((w1, e1), (w2, e2)) = c
  p1 = Equal.cong(Word(32n), U32, x => U32{x}, w, w1, e1)
  p2 = Equal.cong(Word(32n), U32, x => U32{x}, w, w2, e2)
  ((U32{w1}, p1), (U32{w2}, p2))

def U32.copy(u):
  match u:
    case U32{w}:
      U32.copy.go(w, Word.copy(32n, w))

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

def U32.shln(n, a):
  match n:
    case 0n:
      a
    case 1n+p:
      U32.shln(p, U32.shl(a))

def U32.shrn(n, a):
  match n:
    case 0n:
      a
    case 1n+p:
      U32.shrn(p, U32.shr(a))

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

def U32.divmod.go.fin(p, q, s2, b4, g):
  match g:
    case True{}:
      (WCon{True{}, q}, U32.sub(U32{s2}, b4))
    case False{}:
      (WCon{False{}, q}, U32{s2})

def U32.divmod.go.cpy(p, q, t, b3, b4, s, cs):
  ((s1, e5), (s2, e6)) = cs
  U32.divmod.go.fin(p, q, s2, b4, Bool.or(t, U32.is_ge(U32{s1}, b3)))

def U32.divmod.go.shl(p, q, b2, cb2, ts):
  ((b3, e3), (b4, e4)) = cb2
  (t, s) = ts
  U32.divmod.go.cpy(p, q, t, b3, b4, s, Word.copy(32n, s))

def U32.divmod.go.rec(p, a0, b2, qr):
  (q, r) = qr
  U32{rw} = r
  U32.divmod.go.shl(p, q, b2, U32.copy(b2), Word.shl.out(32n, a0, rw))

def U32.divmod.go.con(b, p, a0, hi, cb):
  ((b1, e1), (b2, e2)) = cb
  U32.divmod.go.rec(p, a0, b2, U32.divmod.go(p, hi, b1))

def U32.divmod.go(m, a, b):
  match m a:
    case 0n WNil{}:
      (WNil{}, U32.zero())
    case 1n+p WCon{a0, hi}:
      U32.divmod.go.con(b, p, a0, hi, U32.copy(b))

def U32.div.fin(qr):
  (q, r) = qr
  U32{q}

def U32.div.if(aw, b2, z):
  match z:
    case True{}:
      U32.zero()
    case False{}:
      U32.div.fin(U32.divmod.go(32n, aw, b2))

def U32.div.cpy(aw, b, cb):
  ((b1, e1), (b2, e2)) = cb
  U32.div.if(aw, b2, U32.is_zero(b1))

def U32.div(a, b):
  U32{aw} = a
  U32.div.cpy(aw, b, U32.copy(b))

def U32.mod.fin(qr):
  (q, r) = qr
  r

def U32.mod.if(aw, b2, z):
  match z:
    case True{}:
      U32{aw}
    case False{}:
      U32.mod.fin(U32.divmod.go(32n, aw, b2))

def U32.mod.cpy(aw, b, cb):
  ((b1, e1), (b2, e2)) = cb
  U32.mod.if(aw, b2, U32.is_zero(b1))

def U32.mod(a, b):
  U32{aw} = a
  U32.mod.cpy(aw, b, U32.copy(b))

# F32
# ---

def F32.make(m, s):
  F32.div(U32.to_f32(m), U32.to_f32(s))

# Char
# ----

def Char.copy.go(x, c):
  ((x1, e1), (x2, e2)) = c
  (Chr{x1}, Chr{x2})

def Char.copy(c):
  match c:
    case Chr{x}:
      Char.copy.go(x, U32.copy(x))

def Char.cmp.go(x, y, cx, cy):
  ((x1, e1), (x2, e2)) = cx
  ((y1, f1), (y2, f2)) = cy
  ((Chr{x2}, Chr{y2}), U32.cmp(x1, y1))

def Char.cmp(a, b):
  match a b:
    case Chr{x} Chr{y}:
      Char.cmp.go(x, y, U32.copy(x), U32.copy(y))

# String
# ------

def String.append(a, b):
  match a:
    case SNil{}:
      b
    case SCon{h, t}:
      SCon{h, String.append(t, b)}

def String.copy.con(hh, tt):
  (h1, h2) = hh
  (t1, t2) = tt
  (SCon{h1, t1}, SCon{h2, t2})

def String.copy(s):
  match s:
    case SNil{}:
      (SNil{}, SNil{})
    case SCon{h, t}:
      String.copy.con(Char.copy(h), String.copy(t))

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

def U32.read.dig.if(x4, ok):
  match ok:
    case True{}:
      Some{U32.sub(x4, 48)}
    case False{}:
      None{}

def U32.read.dig.cpy(x1, x2, c2):
  ((x3, e3), (x4, e4)) = c2
  U32.read.dig.if(x4, Bool.and(U32.is_le(48, x1), U32.is_le(x3, 57)))

def U32.read.dig.go(x, c):
  ((x1, e1), (x2, e2)) = c
  U32.read.dig.cpy(x1, x2, U32.copy(x2))

def U32.read.dig(c):
  match c:
    case Chr{x}:
      U32.read.dig.go(x, U32.copy(x))

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

def Nat.show.run(n, c):
  ((n1, e1), (n2, e2)) = c
  Nat.show.go(1n+n1, n2, SNil{})

def Nat.show(n):
  Nat.show.run(n, Nat.copy(n))

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

def U32.show.fin(g, acc, n3, n4, z):
  match z:
    case True{}:
      acc
    case False{}:
      U32.show.go(g, U32.div(n3, 10),
        SCon{Chr{U32.add(48, U32.mod(n4, 10))}, acc})

def U32.show.cpy(g, acc, n1, n2, c2):
  ((n3, e3), (n4, e4)) = c2
  U32.show.fin(g, acc, n3, n4, U32.is_zero(n1))

def U32.show.con(g, acc, n, c):
  ((n1, e1), (n2, e2)) = c
  U32.show.cpy(g, acc, n1, n2, U32.copy(n2))

def U32.show.go(f, n, acc):
  match f:
    case 0n:
      acc
    case 1n+g:
      U32.show.con(g, acc, n, U32.copy(n))

def U32.show.if(a2, z):
  match z:
    case True{}:
      SCon{Chr{48}, SNil{}}
    case False{}:
      U32.show.go(10n, a2, SNil{})

def U32.show.run(a, c):
  ((a1, e1), (a2, e2)) = c
  U32.show.if(a2, U32.is_zero(a1))

def U32.show(a):
  U32.show.run(a, U32.copy(a))

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

def Array.swap.lo(T, ys, r):
  (nxs, old) = r
  (ANode{nxs, ys}, old)

def Array.swap.hi(T, xs, r):
  (nys, old) = r
  (ANode{xs, nys}, old)

def Array.swap.if(T, xs, ys, i2, v, z):
  match z:
    case True{}:
      Array.swap.lo(T, ys, Array.swap(T, xs, U32.shr(i2), v))
    case False{}:
      Array.swap.hi(T, xs, Array.swap(T, ys, U32.shr(i2), v))

def Array.swap.node(T, xs, ys, v, i, ci):
  ((i1, e1), (i2, e2)) = ci
  Array.swap.if(T, xs, ys, i2, v, U32.is_zero(U32.and(i1, U32.one())))

def Array.swap(T, a, i, v):
  match a:
    case ALeaf{x}:
      (ALeaf{v}, x)
    case ANode{xs, ys}:
      Array.swap.node(T, xs, ys, v, i, U32.copy(i))

def Array.copy.leaf(x, c):
  ((x1, e1), (x2, e2)) = c
  (ALeaf{x1}, ALeaf{x2})

def Array.copy.node(cx, cy):
  (xa, xb) = cx
  (ya, yb) = cy
  (ANode{xa, ya}, ANode{xb, yb})

def Array.copy(a):
  match a:
    case ALeaf{x}:
      Array.copy.leaf(x, U32.copy(x))
    case ANode{xs, ys}:
      Array.copy.node(Array.copy(xs), Array.copy(ys))

def Array.new.node(lr):
  (l, r) = lr
  ANode{l, r}

def Array.new(d, v):
  match d:
    case 0n:
      ALeaf{v}
    case 1n+p:
      Array.new.node(Array.copy(Array.new(p, v)))

def Array.set.fin(r):
  (na, old) = r
  na

def Array.set(a, i, v):
  Array.set.fin(Array.swap(U32, a, i, v))

def Array.get.leaf(x, c):
  ((x1, e1), (x2, e2)) = c
  (ALeaf{x1}, x2)

def Array.get.lo(ys, r):
  (nxs, x) = r
  (ANode{nxs, ys}, x)

def Array.get.hi(xs, r):
  (nys, x) = r
  (ANode{xs, nys}, x)

def Array.get.if(xs, ys, i2, z):
  match z:
    case True{}:
      Array.get.lo(ys, Array.get(xs, U32.shr(i2)))
    case False{}:
      Array.get.hi(xs, Array.get(ys, U32.shr(i2)))

def Array.get.node(xs, ys, i, ci):
  ((i1, e1), (i2, e2)) = ci
  Array.get.if(xs, ys, i2, U32.is_zero(U32.and(i1, U32.one())))

def Array.get(a, i):
  match a:
    case ALeaf{x}:
      Array.get.leaf(x, U32.copy(x))
    case ANode{xs, ys}:
      Array.get.node(xs, ys, i, U32.copy(i))

# Map
# ---

def Map.bit.u(x, k):
  U32.is_ne(U32.and(U32.shrn(k, x), 1), 0)

def Map.bit.chr.go(b, x, c):
  ((x1, e1), (x2, e2)) = c
  (Chr{x1}, Map.bit.u(x2, Nat.sub(31n, b)))

def Map.bit.chr(c, off):
  match c:
    case Chr{x}:
      match off:
        case 0n:
          (Chr{x}, True{})
        case 1n+b:
          Map.bit.chr.go(b, x, U32.copy(x))

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

def Map.msb.u.go(p, x, c):
  ((x1, e1), (x2, e2)) = c
  Map.msb.u.if(p, x2, U32.is_zero(x1))

def Map.msb.u(n, x):
  match n:
    case 0n:
      0n
    case 1n+p:
      Map.msb.u.go(p, x, U32.copy(x))

def Map.diff.chr(x):
  Nat.sub(33n, Map.msb.u(32n, x))

def Map.diff.step.go(cx, cy, ax, ay):
  ((cx1, e1), (cx2, e2)) = ax
  ((cy1, f1), (cy2, f2)) = ay
  (Map.diff.chr(U32.xor(cx2, cy2)), U32.is_eq(cx1, cy1))

def Map.diff.step(x, y):
  match x y:
    case Chr{cx} Chr{cy}:
      Map.diff.step.go(cx, cy, U32.copy(cx), U32.copy(cy))

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

def Map.new(V):
  MTip{}

def Map.put.bit(V, x, p2, lo, hi, kb):
  (key2, b) = kb
  match b:
    case False{}:
      MNode{p2, Map.put(V, lo, key2, x), hi}
    case True{}:
      MNode{p2, lo, Map.put(V, hi, key2, x)}

def Map.put.node(V, key, x, lo, hi, pos, cq):
  ((p1, e1), (p2, e2)) = cq
  Map.put.bit(V, x, p2, lo, hi, Map.bit(key, p1))

def Map.put(V, m, key, x):
  match m:
    case MTip{}:
      MLeaf{key, x}
    case MLeaf{k, v}:
      MLeaf{k, x}
    case MNode{pos, lo, hi}:
      Map.put.node(V, key, x, lo, hi, pos, Nat.copy(pos))

def Map.ins.splice.bit(V, x, rest, pb, kb):
  (key2, b) = kb
  match b:
    case False{}:
      MNode{pb, MLeaf{key2, x}, rest}
    case True{}:
      MNode{pb, rest, MLeaf{key2, x}}

def Map.ins.splice.cpy(V, key, x, rest, p, cq):
  ((pa, e1), (pb, e2)) = cq
  Map.ins.splice.bit(V, x, rest, pb, Map.bit(key, pa))

def Map.ins.splice(V, p, key, x, rest):
  Map.ins.splice.cpy(V, key, x, rest, p, Nat.copy(p))

def Map.ins.deep(V, x, lo, hi, pb, qb, kb):
  (key2, b) = kb
  match b:
    case False{}:
      MNode{qb, Map.ins(V, lo, key2, x, pb), hi}
    case True{}:
      MNode{qb, lo, Map.ins(V, hi, key2, x, pb)}

def Map.ins.down(V, key, x, lo, hi, pb, pos2, cq):
  ((qa, g1), (qb, g2)) = cq
  Map.ins.deep(V, x, lo, hi, pb, qb, Map.bit(key, qa))

def Map.ins.if(V, key, x, lo, hi, pos2, pb, t):
  match t:
    case False{}:
      Map.ins.splice(V, pb, key, x, MNode{pos2, lo, hi})
    case True{}:
      Map.ins.down(V, key, x, lo, hi, pb, pos2, Nat.copy(pos2))

def Map.ins.node(V, key, x, lo, hi, pos, p, cpos, cp2):
  ((pos1, e1), (pos2, e2)) = cpos
  ((pa, f1), (pb, f2)) = cp2
  Map.ins.if(V, key, x, lo, hi, pos2, pb, Nat.is_lt(pos1, pa))

def Map.ins(V, m, key, x, p):
  match m:
    case MTip{}:
      MLeaf{key, x}
    case MLeaf{k, v}:
      Map.ins.splice(V, p, key, x, MLeaf{k, v})
    case MNode{pos, lo, hi}:
      Map.ins.node(V, key, x, lo, hi, pos, p, Nat.copy(pos), Nat.copy(p))

def Map.seek.leaf(V, v, key, kk):
  (k1, k2) = kk
  ((MLeaf{k1, v}, key), Some{k2})

def Map.seek.lo(V, p2, hi, r0):
  ((lo2, key3), r) = r0
  ((MNode{p2, lo2, hi}, key3), r)

def Map.seek.hi(V, p2, lo, r0):
  ((hi2, key3), r) = r0
  ((MNode{p2, lo, hi2}, key3), r)

def Map.seek.bit(V, lo, hi, p2, kb):
  (key2, b) = kb
  match b:
    case False{}:
      Map.seek.lo(V, p2, hi, Map.seek(V, lo, key2))
    case True{}:
      Map.seek.hi(V, p2, lo, Map.seek(V, hi, key2))

def Map.seek.node(V, key, lo, hi, pos, cq):
  ((p1, e1), (p2, e2)) = cq
  Map.seek.bit(V, lo, hi, p2, Map.bit(key, p1))

def Map.seek(V, m, key):
  match m:
    case MTip{}:
      ((MTip{}, key), None{})
    case MLeaf{k, v}:
      Map.seek.leaf(V, v, key, String.copy(k))
    case MNode{pos, lo, hi}:
      Map.seek.node(V, key, lo, hi, pos, Nat.copy(pos))

def Map.set.fin.go(V, m, key, x, r):
  ((keyb2, k2), c) = r
  match c:
    case LT{}:
      Map.ins(V, m, key, x, Map.diff(keyb2, k2))
    case EQ{}:
      Map.put(V, m, key, x)
    case GT{}:
      Map.ins(V, m, key, x, Map.diff(keyb2, k2))

def Map.set.fin(V, m, key, x, keyb, k):
  Map.set.fin.go(V, m, key, x, String.cmp(keyb, k))

def Map.set.some(V, m2, x, k, kk):
  (ka, kb) = kk
  Map.set.fin(V, m2, ka, x, kb, k)

def Map.set.go(V, x, r):
  ((m2, key2), found) = r
  match found:
    case None{}:
      MLeaf{key2, x}
    case Some{k}:
      Map.set.some(V, m2, x, k, String.copy(key2))

def Map.set(V, m, key, x):
  Map.set.go(V, x, Map.seek(V, m, key))

def Map.set.kv(V, m, kv):
  (k, v) = kv
  Map.set(V, m, k, v)

def Map.has.leaf(V, v, r):
  ((key2, k2), c) = r
  (MLeaf{k2, v}, Cmp.is_eq(c))

def Map.has.lo(V, p2, hi, r0):
  (lo2, r) = r0
  (MNode{p2, lo2, hi}, r)

def Map.has.hi(V, p2, lo, r0):
  (hi2, r) = r0
  (MNode{p2, lo, hi2}, r)

def Map.has.bit(V, lo, hi, p2, kb):
  (key2, b) = kb
  match b:
    case False{}:
      Map.has.lo(V, p2, hi, Map.has(V, lo, key2))
    case True{}:
      Map.has.hi(V, p2, lo, Map.has(V, hi, key2))

def Map.has.node(V, key, lo, hi, pos, cq):
  ((p1, e1), (p2, e2)) = cq
  Map.has.bit(V, lo, hi, p2, Map.bit(key, p1))

def Map.has(V, m, key):
  match m:
    case MTip{}:
      (MTip{}, False{})
    case MLeaf{k, v}:
      Map.has.leaf(V, v, String.cmp(key, k))
    case MNode{pos, lo, hi}:
      Map.has.node(V, key, lo, hi, pos, Nat.copy(pos))

def Map.get.eq(V, k2, vv):
  (v1, v2) = vv
  (MLeaf{k2, v1}, v2)

def Map.get.leaf(V, cp, d, v, r):
  ((key2, k2), c) = r
  match c:
    case LT{}:
      (MLeaf{k2, v}, d)
    case EQ{}:
      Map.get.eq(V, k2, cp(v))
    case GT{}:
      (MLeaf{k2, v}, d)

def Map.get.lo(V, p2, hi, r0):
  (lo2, r) = r0
  (MNode{p2, lo2, hi}, r)

def Map.get.hi(V, p2, lo, r0):
  (hi2, r) = r0
  (MNode{p2, lo, hi2}, r)

def Map.get.bit(V, cp, d, lo, hi, p2, kb):
  (key2, b) = kb
  match b:
    case False{}:
      Map.get.lo(V, p2, hi, Map.get(V, cp, d, lo, key2))
    case True{}:
      Map.get.hi(V, p2, lo, Map.get(V, cp, d, hi, key2))

def Map.get.node(V, cp, d, key, lo, hi, pos, cq):
  ((p1, e1), (p2, e2)) = cq
  Map.get.bit(V, cp, d, lo, hi, p2, Map.bit(key, p1))

def Map.get(V, cp, d, m, key):
  match m:
    case MTip{}:
      (MTip{}, d)
    case MLeaf{k, v}:
      Map.get.leaf(V, cp, d, v, String.cmp(key, k))
    case MNode{pos, lo, hi}:
      Map.get.node(V, cp, d, key, lo, hi, pos, Nat.copy(pos))

def Map.pop.lo(V, pos, lo, hi, r):
  match lo:
    case MTip{}:
      (hi, r)
    case MLeaf{k, v}:
      (MNode{pos, MLeaf{k, v}, hi}, r)
    case MNode{p, a, b}:
      (MNode{pos, MNode{p, a, b}, hi}, r)

def Map.pop.hi(V, pos, lo, hi, r):
  match hi:
    case MTip{}:
      (lo, r)
    case MLeaf{k, v}:
      (MNode{pos, lo, MLeaf{k, v}}, r)
    case MNode{p, a, b}:
      (MNode{pos, lo, MNode{p, a, b}}, r)

def Map.pop.leaf(V, v, r):
  ((key2, k2), c) = r
  match c:
    case LT{}:
      (MLeaf{k2, v}, None{})
    case EQ{}:
      (MTip{}, Some{v})
    case GT{}:
      (MLeaf{k2, v}, None{})

def Map.pop.golo(V, p2, hi, r0):
  (lo2, r) = r0
  Map.pop.lo(V, p2, lo2, hi, r)

def Map.pop.gohi(V, p2, lo, r0):
  (hi2, r) = r0
  Map.pop.hi(V, p2, lo, hi2, r)

def Map.pop.bit(V, lo, hi, p2, kb):
  (key2, b) = kb
  match b:
    case False{}:
      Map.pop.golo(V, p2, hi, Map.pop(V, lo, key2))
    case True{}:
      Map.pop.gohi(V, p2, lo, Map.pop(V, hi, key2))

def Map.pop.node(V, key, lo, hi, pos, cq):
  ((p1, e1), (p2, e2)) = cq
  Map.pop.bit(V, lo, hi, p2, Map.bit(key, p1))

def Map.pop(V, m, key):
  match m:
    case MTip{}:
      (MTip{}, None{})
    case MLeaf{k, v}:
      Map.pop.leaf(V, v, String.cmp(key, k))
    case MNode{pos, lo, hi}:
      Map.pop.node(V, key, lo, hi, pos, Nat.copy(pos))

def Map.del.fin(V, r):
  (m2, x) = r
  m2

def Map.del(V, m, key):
  Map.del.fin(V, Map.pop(V, m, key))

def Map.to_list.go(V, m, acc):
  match m:
    case MTip{}:
      acc
    case MLeaf{k, v}:
      Con{(k, v), acc}
    case MNode{pos, lo, hi}:
      Map.to_list.go(V, lo, Map.to_list.go(V, hi, acc))

def Map.to_list(V, m):
  Map.to_list.go(V, m, Nil{})

def Map.keys.go(V, m, acc):
  match m:
    case MTip{}:
      acc
    case MLeaf{k, v}:
      Con{k, acc}
    case MNode{pos, lo, hi}:
      Map.keys.go(V, lo, Map.keys.go(V, hi, acc))

def Map.keys(V, m):
  Map.keys.go(V, m, Nil{})

def Map.from_list.go(V, kvs, m):
  match kvs:
    case Nil{}:
      m
    case Con{kv, t}:
      Map.from_list.go(V, t, Map.set.kv(V, m, kv))

def Map.from_list(V, kvs):
  Map.from_list.go(V, kvs, MTip{})

def Map.union(V, a, b):
  Map.from_list.go(V, Map.to_list(V, b), a)

# Set
# ---

def Set():
  Map<Unit>

def Set.new():
  Map.new(Unit)

def Set.add(s, key):
  Map.set(Unit, s, key, Unit{})

def Set.has(s, key):
  Map.has(Unit, s, key)

def Set.del(s, key):
  Map.del(Unit, s, key)

def Set.union(a, b):
  Map.union(Unit, a, b)
