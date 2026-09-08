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

law Word:
  for n: Nat
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

type Image is Data:
  Pix{color: U32}
  Qua{tl: Image, tr: Image, bl: Image, br: Image}

type Event is Data:
  Key{code: U32, down: Bool}
  Mouse{x: U32, y: U32, button: U32, down: Bool}
  Move{x: U32, y: U32}
  Close{}

# Effects
# -------

type File is Type:
  File{slot: U32, gen: U32}

type Socket is Type:
  Socket{slot: U32, gen: U32}

type Listener is Type:
  Listener{slot: U32, gen: U32}

type Window is Type:
  Window{slot: U32, gen: U32}

type Chan<-A: Type> is Data:
  Chan{slot: U32, gen: U32}

type IO.OP<-R: Type> is Type:
  Emit{value: R}
  Halt{code: U32, message: String}

law Pair:
  for -A: Type
  for -B: Type
  Type

law IO:
  for -A: Type
  Type

type App<-S: Type> is Type:
  App{view: S -> Pair(S, Image), tick: List<Event> -> S -> IO(Maybe<S>)}

# Map
# ---

type Map<a, -V: Kind(a)> is Kind(a):
  MTip{}
  MLeaf{key: String, val: V}
  MNode{pos: Nat, lo: Map<a, V>, hi: Map<a, V>}

# Defs
# ====

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

def Exists(-A: Type, -B: @-x: A -> Type) -> Type:
  Sigma<&1, &1, A, B>

def Or(-A: Type, -B: Type) -> Type:
  Either<&1, &1, A, B>

# Effects
# -------

def IO(A):
  @-R: Type ->
  @k: (A -> IO.OP<R>) ->
  IO.OP<R>

def IO.pure(-A: Type, x: A) -> IO(A):
  R => k => k(x)

def IO.bind(-A: Type, -B: Type, m: IO(A), f: A -> IO(B)) -> IO(B):
  R => k => m(R, x => f(x, R, k))

def IO.print(text: String) -> IO(Unit):
  import "./effs/print.c"
  import "./effs/print.js"

def IO.write(text: String) -> IO(Unit):
  import "./effs/write.c"
  import "./effs/write.js"

def IO.print_err(text: String) -> IO(Unit):
  import "./effs/print_err.c"
  import "./effs/print_err.js"

def IO.get_env(name: String) -> IO(Result<&1, &1, U32 & String, String>):
  import "./effs/get_env.c"
  import "./effs/get_env.js"

def IO.die(-A: Type, code: U32, msg: String) -> IO(A):
  R => k => Halt{code, msg}

def IO.pass(-A: Type, r: Result<&1, &1, U32 & String, A>) -> IO(A):
  match r:
    case Done{value}:
      IO.pure(A, value)
    case Fail{(code, message)}:
      IO.die(A, code, message)

def IO.try(-A: Type, act: IO(Result<&1, &1, U32 & String, A>)) -> IO(A):
  IO.bind(Result<&1, &1, U32 & String, A>, A, act, IO.pass(A))

def IO.spawn(-A: Type, act: IO(A)) -> IO(Unit):
  import "./effs/spawn.c"
  import "./effs/spawn.js"

def IO.sleep(ms: U32) -> IO(Unit):
  import "./effs/sleep.c"
  import "./effs/sleep.js"

def IO.now() -> IO(Nat):
  import "./effs/now.c"
  import "./effs/now.js"

def Chan.new(-A: Type, room: U32) -> IO(Chan<A>):
  import "./effs/chan_new.c"
  import "./effs/chan_new.js"

def Chan.send(-A: Type, chan: Chan<A>, value: A) -> IO(Bool):
  import "./effs/chan_send.c"
  import "./effs/chan_send.js"

def Chan.recv(-A: Type, chan: Chan<A>) -> IO(Maybe<&1, A>):
  import "./effs/chan_recv.c"
  import "./effs/chan_recv.js"

def Chan.close(-A: Type, chan: Chan<A>) -> IO(Unit):
  import "./effs/chan_close.c"
  import "./effs/chan_close.js"

def IO.fork.go(-A: Type, act: IO(A), chan: Chan<A>) -> IO(Chan<A>):
  +c = chan
  sent = IO.bind(A, Bool, act, x => Chan.send(A, c, x))
  IO.bind(Unit, Chan<A>, IO.spawn(Bool, sent), u => IO.pure(Chan<A>, c))

def IO.fork(-A: Type, act: IO(A)) -> IO(Chan<A>):
  IO.bind(Chan<A>, Chan<A>, Chan.new(A, 1), IO.fork.go(A, act))

def IO.join.go(-A: Type, chan: Chan<A>, got: Maybe<&1, A>) -> IO(A):
  match got:
    case None{}:
      IO.die(A, 1, "IO.join: the channel was closed")
    case Some{value}:
      IO.bind(Unit, A, Chan.close(A, chan), u => IO.pure(A, value))

def IO.join(-A: Type, chan: Chan<A>) -> IO(A):
  +c = chan
  IO.bind(Maybe<&1, A>, A, Chan.recv(A, c), IO.join.go(A, c))

def File.open(path: String, mode: String) ->
  IO(Result<&1, &1, U32 & String, File>):
  import "./effs/file_open.c"
  import "./effs/file_open.js"

def File.read(file: File, max: U32) ->
  IO(File & Result<&1, &1, U32 & String, String>):
  import "./effs/file_read.c"
  import "./effs/file_read.js"

def File.write(file: File, data: String) ->
  IO(File & Result<&1, &1, U32 & String, Unit>):
  import "./effs/file_write.c"
  import "./effs/file_write.js"

def File.close(file: File) -> IO(Unit):
  import "./effs/file_close.c"
  import "./effs/file_close.js"

def TCP.listen(port: U32) -> IO(Result<&1, &1, U32 & String, Listener>):
  import "./effs/tcp_listen.c"
  import "./effs/tcp_listen.js"

def TCP.accept(listener: Listener) ->
  IO(Listener & Result<&1, &1, U32 & String, Socket>):
  import "./effs/tcp_accept.c"
  import "./effs/tcp_accept.js"

def TCP.connect(host: String, port: U32) ->
  IO(Result<&1, &1, U32 & String, Socket>):
  import "./effs/tcp_connect.c"
  import "./effs/tcp_connect.js"

def TCP.send(sock: Socket, data: String) ->
  IO(Socket & Result<&1, &1, U32 & String, Unit>):
  import "./effs/tcp_send.c"
  import "./effs/tcp_send.js"

def TCP.recv(sock: Socket, max: U32) ->
  IO(Socket & Result<&1, &1, U32 & String, String>):
  import "./effs/tcp_recv.c"
  import "./effs/tcp_recv.js"

def UDP.bind(port: U32) -> IO(Result<&1, &1, U32 & String, Socket>):
  import "./effs/udp_bind.c"
  import "./effs/udp_bind.js"

def UDP.send_to(sock: Socket, host: String, port: U32, data: String) ->
  IO(Socket & Result<&1, &1, U32 & String, Unit>):
  import "./effs/udp_send_to.c"
  import "./effs/udp_send_to.js"

def UDP.recv_from(sock: Socket, max: U32) ->
  IO(Socket & Result<&1, &1, U32 & String, String & U32 & String>):
  import "./effs/udp_recv_from.c"
  import "./effs/udp_recv_from.js"

def Socket.close(socket: Socket) -> IO(Unit):
  import "./effs/socket_close.c"
  import "./effs/socket_close.js"

def Listener.close(listener: Listener) -> IO(Unit):
  import "./effs/listener_close.c"
  import "./effs/listener_close.js"

def Window.open(title: String, width: U32, height: U32) ->
  IO(Result<&1, &1, U32 & String, Window>):
  import "./effs/window_open.c"
  import "./effs/window_open.js"

def Window.frame(window: Window, image: Image) ->
  IO(Window & Image & List<Event>):
  import "./effs/window_frame.c"
  import "./effs/window_frame.js"

def Window.close(window: Window) -> IO(Unit):
  import "./effs/window_close.c"
  import "./effs/window_close.js"

# Equal
# -----

law Equal.cong:
  for -A: Type
  for -B: Type
  for -f: A -> B
  for -a: A
  for -b: A
  for  e: {a == b : A}
  {f(a) == f(b) : B}

def Equal.cong(A, B, f, a, b, e):
  %e : {f(a) == f(_) : B}
  {==}

law Equal.sym:
  for -A: Type
  for -a: A
  for -b: A
  for  e: {a == b : A}
  {b == a : A}

def Equal.sym(A, a, b, e):
  %e : {_ == a : A}
  {==}

law Equal.trans:
  for -A : Type
  for -a : A
  for -b : A
  for -c : A
  for ab : {a == b : A}
  for bc : {b == c : A}
  {a == c : A}

def Equal.trans(A, a, b, c, ab, bc):
  %bc : {a == _ : A}
  ab

# Empty
# -----

def Empty.absurd(-A: Type, e: Empty) -> A:
  match e:

# Bool
# ----

def Bool.not(b: Bool) -> Bool:
  match b:
    case False{}:
      True{}
    case True{}:
      False{}

def Bool.and(a: Bool, b: Bool) -> Bool:
  match a:
    case False{}:
      False{}
    case True{}:
      b

def Bool.or(a: Bool, b: Bool) -> Bool:
  match a:
    case False{}:
      b
    case True{}:
      True{}

def Bool.xor(a: Bool, b: Bool) -> Bool:
  match a:
    case False{}:
      b
    case True{}:
      Bool.not(b)

def Bool.cmp(a: Bool, b: Bool) -> Cmp:
  match a b:
    case False{} False{}:
      EQ{}
    case False{} True{}:
      LT{}
    case True{} False{}:
      GT{}
    case True{} True{}:
      EQ{}

def Bool.full_add(a: Bool, b: Bool, c: Bool) -> Bool & Bool:
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

def Cmp.is_lt(c: Cmp) -> Bool:
  match c:
    case LT{}:
      True{}
    case EQ{}:
      False{}
    case GT{}:
      False{}

def Cmp.is_eq(c: Cmp) -> Bool:
  match c:
    case LT{}:
      False{}
    case EQ{}:
      True{}
    case GT{}:
      False{}

def Cmp.is_gt(c: Cmp) -> Bool:
  match c:
    case LT{}:
      False{}
    case EQ{}:
      False{}
    case GT{}:
      True{}

def Cmp.is_le(c: Cmp) -> Bool:
  match c:
    case LT{}:
      True{}
    case EQ{}:
      True{}
    case GT{}:
      False{}

def Cmp.is_ge(c: Cmp) -> Bool:
  match c:
    case LT{}:
      False{}
    case EQ{}:
      True{}
    case GT{}:
      True{}

# Nat
# ---

def Nat.double(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      2n+Nat.double(p)

def Nat.add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n+p:
      1n+Nat.add(p, b)

def Nat.sub(a: Nat, b: Nat) -> Nat:
  match a b:
    case 0n 0n:
      0n
    case 0n 1n+bp:
      0n
    case 1n+ap 0n:
      1n+ap
    case 1n+ap 1n+bp:
      Nat.sub(ap, bp)

def Nat.mul(a: Nat, +b: Nat) -> Nat:
  match a:
    case 0n:
      0n
    case 1n+p:
      Nat.add(b, Nat.mul(p, b))

def Nat.divmod.go(n: Nat, m: Nat, d: Nat, r: Nat) -> Nat & Nat:
  match n:
    case 0n:
      (d, r)
    case 1n+np:
      match m:
        case 0n:
          Nat.divmod.go(np, r, 1n+d, 0n)
        case 1n+mp:
          Nat.divmod.go(np, mp, d, 1n+r)

def Nat.divmod(a: Nat, b: Nat) -> Nat & Nat:
  match b:
    case 0n:
      (0n, a)
    case 1n+bp:
      Nat.divmod.go(a, bp, 0n, 0n)

def Nat.cmp(a: Nat, b: Nat) -> Cmp:
  match a b:
    case 0n 0n:
      EQ{}
    case 0n 1n+bp:
      LT{}
    case 1n+ap 0n:
      GT{}
    case 1n+ap 1n+bp:
      Nat.cmp(ap, bp)

def Nat.is_lt(a: Nat, b: Nat) -> Bool:
  Cmp.is_lt(Nat.cmp(a, b))

# Maybe
# -----

def Maybe.pure(a, -A: Kind(a), x: A) -> Maybe<a, A>:
  Some{x}

def Maybe.bind(
  a, -A: Kind(a), -B: Kind(a), m: Maybe<a, A>, f: A -> Maybe<a, B>
) -> Maybe<a, B>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      f(x)

# Result
# ------

def Result.pure(a, b, -E: Kind(a), -A: Kind(b), x: A) -> Result<a, b, E, A>:
  Done{x}

def Result.fail(a, b, -E: Kind(a), -A: Kind(b), e: E) -> Result<a, b, E, A>:
  Fail{e}

def Result.bind(
  a, b, -E: Kind(a), -A: Kind(b), -B: Kind(b), r: Result<a, b, E, A>,
  f: A -> Result<a, b, E, B>
) -> Result<a, b, E, B>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      f(x)

# List
# ----

def List.map(~A: Type, ~B: Type, ~f: A -> B, xs: List<A>) -> List<B>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{f(h), List.map(~A, ~B, ~f, t)}

# Word
# ----

def Word.cast(-m: Nat, -n: Nat, e: {m == n : Nat}, w: Word(m)) -> Word(n):
  %e : Word(_)
  w

def Word.zero(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{False{}, Word.zero(p)}

def Word.not(n: Nat, w: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{Bool.not(b), Word.not(p, t)}

def Word.and(n: Nat, a: Word(n), b: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          WCon{Bool.and(ab, bb), Word.and(p, at, bt)}

def Word.or(n: Nat, a: Word(n), b: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          WCon{Bool.or(ab, bb), Word.or(p, at, bt)}

def Word.xor(n: Nat, a: Word(n), b: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          WCon{Bool.xor(ab, bb), Word.xor(p, at, bt)}

def Word.shl.put(n: Nat, c: Bool, w: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{c, Word.shl.put(p, b, t)}

def Word.shl(n: Nat, w: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{False{}, Word.shl.put(p, b, t)}

def Word.shl.out.con(-p: Nat, c: Bool, r: Bool & Word(p)) -> Bool & Word(1n+p):
  (hi, t2) = r
  (hi, WCon{c, t2})

def Word.shl.out(n: Nat, c: Bool, w: Word(n)) -> Bool & Word(n):
  match n:
    case 0n:
      (c, WNil{})
    case 1n+p:
      match w:
        case WCon{b, t}:
          Word.shl.out.con(p, c, Word.shl.out(p, b, t))

def Word.shr.pad(n: Nat, w: Word(n)) -> Word(1n+n):
  match n:
    case 0n:
      WCon{False{}, w}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{b, Word.shr.pad(p, t)}

def Word.shr(n: Nat, w: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          Word.shr.pad(p, t)

def Word.cmp.fin(ab: Bool, bb: Bool, t: Cmp) -> Cmp:
  match t:
    case LT{}:
      LT{}
    case EQ{}:
      Bool.cmp(ab, bb)
    case GT{}:
      GT{}

def Word.cmp(n: Nat, a: Word(n), b: Word(n)) -> Cmp:
  match n:
    case 0n:
      EQ{}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          Word.cmp.fin(ab, bb, Word.cmp(p, at, bt))

def Word.inc(n: Nat, w: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          WCon{True{}, t}
        case WCon{True{}, t}:
          WCon{False{}, Word.inc(p, t)}

law Word.adc:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for f: Bool
  for c: Bool
  Word(n)

def Word.adc.con(p: Nat, at: Word(p), bt: Word(p), f: Bool, sk: Bool & Bool) ->
  Word(1n+p):
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

def Word.add(n: Nat, a: Word(n), b: Word(n)) -> Word(n):
  Word.adc(n, a, b, False{}, False{})

def Word.sub(n: Nat, a: Word(n), b: Word(n)) -> Word(n):
  Word.adc(n, a, b, True{}, True{})

law Word.add_comm.arm:
  for p  : Nat
  for -h : Bool
  for at : Word(p)
  for bt : Word(p)
  for k  : Bool
  {WCon{h, Word.adc(p, at, bt, False{}, k)}
    == WCon{h, Word.adc(p, bt, at, False{}, k)} : Word.Con<p>}

law Word.add_comm.go:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for c: Bool
  {Word.adc(n, a, b, False{}, c) == Word.adc(n, b, a, False{}, c) : Word(n)}

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

law Word.add_comm:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  {Word.add(n, a, b) == Word.add(n, b, a) : Word(n)}

def Word.add_comm(n, a, b):
  Word.add_comm.go(n, a, b, False{})

def Word.to_nat(n: Nat, w: Word(n)) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          Nat.double(Word.to_nat(p, t))
        case WCon{True{}, t}:
          1n+Nat.double(Word.to_nat(p, t))

def Word.mul.go(+n: Nat, m: Nat, a: Word(m), b: Word(n), acc: Word(n)) ->
  Word(n):
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

def Word.mul(+n: Nat, a: Word(n), b: Word(n)) -> Word(n):
  Word.mul.go(n, n, a, b, Word.zero(n))

# U32
# ---

def U32.zero() -> U32:
  U32{Word.zero(32n)}

def U32.one() -> U32:
  U32{Word.inc(32n, Word.zero(32n))}

def U32.inc(a: U32) -> U32:
  match a:
    case U32{x}:
      U32{Word.inc(32n, x)}

def U32.add(a: U32, b: U32) -> U32:
  match a b:
    case U32{x} U32{y}:
      U32{Word.add(32n, x, y)}

law U32.add_comm:
  for a: U32
  for b: U32
  {U32.add(a, b) == U32.add(b, a) : U32}

def U32.add_comm(a, b):
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.add(32n, x, y),
        Word.add(32n, y, x), Word.add_comm(32n, x, y))

def U32.sub(a: U32, b: U32) -> U32:
  match a b:
    case U32{x} U32{y}:
      U32{Word.sub(32n, x, y)}

def U32.mul(a: U32, b: U32) -> U32:
  match a b:
    case U32{x} U32{y}:
      U32{Word.mul(32n, x, y)}

def U32.not(a: U32) -> U32:
  match a:
    case U32{x}:
      U32{Word.not(32n, x)}

def U32.and(a: U32, b: U32) -> U32:
  match a b:
    case U32{x} U32{y}:
      U32{Word.and(32n, x, y)}

def U32.or(a: U32, b: U32) -> U32:
  match a b:
    case U32{x} U32{y}:
      U32{Word.or(32n, x, y)}

def U32.xor(a: U32, b: U32) -> U32:
  match a b:
    case U32{x} U32{y}:
      U32{Word.xor(32n, x, y)}

def U32.shl(a: U32) -> U32:
  match a:
    case U32{x}:
      U32{Word.shl(32n, x)}

def U32.shr(a: U32) -> U32:
  match a:
    case U32{x}:
      U32{Word.shr(32n, x)}

def U32.shln(a: U32, n: Nat) -> U32:
  match n:
    case 0n:
      a
    case 1n+p:
      U32.shl(U32.shln(a, p))

def U32.shrn(a: U32, n: Nat) -> U32:
  match n:
    case 0n:
      a
    case 1n+p:
      U32.shr(U32.shrn(a, p))

def U32.cmp(a: U32, b: U32) -> Cmp:
  match a b:
    case U32{x} U32{y}:
      Word.cmp(32n, x, y)

def U32.is_eq(a: U32, b: U32) -> Bool:
  Cmp.is_eq(U32.cmp(a, b))

def U32.is_ne(a: U32, b: U32) -> Bool:
  Bool.not(Cmp.is_eq(U32.cmp(a, b)))

def U32.is_lt(a: U32, b: U32) -> Bool:
  Cmp.is_lt(U32.cmp(a, b))

def U32.is_le(a: U32, b: U32) -> Bool:
  Cmp.is_le(U32.cmp(a, b))

def U32.is_gt(a: U32, b: U32) -> Bool:
  Cmp.is_gt(U32.cmp(a, b))

def U32.is_ge(a: U32, b: U32) -> Bool:
  Cmp.is_ge(U32.cmp(a, b))

def U32.is_zero(a: U32) -> Bool:
  U32.is_eq(a, U32.zero())

def U32.to_nat(a: U32) -> Nat:
  match a:
    case U32{w}:
      Word.to_nat(32n, w)

def U32.from_nat(n: Nat) -> U32:
  match n:
    case 0n:
      U32.zero()
    case 1n+p:
      U32.inc(U32.from_nat(p))

def U32.divmod.go.fin(-p: Nat, q: Word(p), s: U32, b: U32, g: Bool) ->
  Word(1n+p) & U32:
  match g:
    case True{}:
      (WCon{True{}, q}, U32.sub(s, b))
    case False{}:
      (WCon{False{}, q}, s)

def U32.divmod.go.shl(-p: Nat, q: Word(p), +b: U32, ts: Bool & Word(32n)) ->
  Word(1n+p) & U32:
  (t, s) = ts
  +s2 = {U32{s} : U32}
  U32.divmod.go.fin(p, q, s2, b, Bool.or(t, U32.is_ge(s2, b)))

def U32.divmod.go.rec(-p: Nat, a0: Bool, +b: U32, qr: Word(p) & U32) ->
  Word(1n+p) & U32:
  (q, r) = qr
  U32{rw} = r
  U32.divmod.go.shl(p, q, b, Word.shl.out(32n, a0, rw))

def U32.divmod.go(m: Nat, a: Word(m), +b: U32) -> Word(m) & U32:
  match m a:
    case 0n WNil{}:
      (WNil{}, U32.zero())
    case 1n+p WCon{a0, hi}:
      U32.divmod.go.rec(p, a0, b, U32.divmod.go(p, hi, b))

def U32.div.fin(qr: Word(32n) & U32) -> U32:
  (q, r) = qr
  U32{q}

def U32.div.if(aw: Word(32n), b: U32, z: Bool) -> U32:
  match z:
    case True{}:
      U32.zero()
    case False{}:
      U32.div.fin(U32.divmod.go(32n, aw, b))

def U32.div(a: U32, +b: U32) -> U32:
  U32{aw} = a
  U32.div.if(aw, b, U32.is_zero(b))

def U32.mod.fin(qr: Word(32n) & U32) -> U32:
  (q, r) = qr
  r

def U32.mod.if(aw: Word(32n), b: U32, z: Bool) -> U32:
  match z:
    case True{}:
      U32{aw}
    case False{}:
      U32.mod.fin(U32.divmod.go(32n, aw, b))

def U32.mod(a: U32, +b: U32) -> U32:
  U32{aw} = a
  U32.mod.if(aw, b, U32.is_zero(b))

# F32
# ---

law U32.to_f32:
  for a: U32
  F32

law F32.to_u32:
  for a: F32
  U32

law F32.add:
  for a: F32
  for b: F32
  F32

law F32.sub:
  for a: F32
  for b: F32
  F32

law F32.mul:
  for a: F32
  for b: F32
  F32

law F32.div:
  for a: F32
  for b: F32
  F32

law F32.mod:
  for a: F32
  for b: F32
  F32

law F32.pow:
  for a: F32
  for b: F32
  F32

law F32.atan2:
  for a: F32
  for b: F32
  F32

law F32.neg:
  for a: F32
  F32

law F32.abs:
  for a: F32
  F32

law F32.sqrt:
  for a: F32
  F32

law F32.exp:
  for a: F32
  F32

law F32.log:
  for a: F32
  F32

law F32.log2:
  for a: F32
  F32

law F32.log10:
  for a: F32
  F32

law F32.sin:
  for a: F32
  F32

law F32.cos:
  for a: F32
  F32

law F32.tan:
  for a: F32
  F32

law F32.asin:
  for a: F32
  F32

law F32.acos:
  for a: F32
  F32

law F32.atan:
  for a: F32
  F32

law F32.sinh:
  for a: F32
  F32

law F32.cosh:
  for a: F32
  F32

law F32.tanh:
  for a: F32
  F32

law F32.floor:
  for a: F32
  F32

law F32.ceil:
  for a: F32
  F32

law F32.trunc:
  for a: F32
  F32

law F32.is_eq:
  for a: F32
  for b: F32
  Bool

law F32.is_ne:
  for a: F32
  for b: F32
  Bool

law F32.is_lt:
  for a: F32
  for b: F32
  Bool

law F32.is_le:
  for a: F32
  for b: F32
  Bool

law F32.is_gt:
  for a: F32
  for b: F32
  Bool

law F32.is_ge:
  for a: F32
  for b: F32
  Bool

law F32.show:
  for +a: F32
  String

law F32.read:
  for s: String
  Maybe<&2, F32>

# Char
# ----

def Char.cmp(a: Char, b: Char) -> (Char & Char) & Cmp:
  match a b:
    case Chr{x} Chr{y}:
      +x2 = x
      +y2 = y
      ((Chr{x2}, Chr{y2}), U32.cmp(x2, y2))

# String
# ------

def String.append(a: String, b: String) -> String:
  match a:
    case SNil{}:
      b
    case SCon{h, t}:
      SCon{h, String.append(t, b)}

def String.cmp.rec(h1b: Char, h2b: Char, rr: (String & String) & Cmp) ->
  (String & String) & Cmp:
  ((t1b, t2b), r) = rr
  ((SCon{h1b, t1b}, SCon{h2b, t2b}), r)

law String.cmp:
  for a: String
  for b: String
  (String & String) & Cmp

def String.cmp.fin(t1: String, t2: String, hc: (Char & Char) & Cmp) ->
  (String & String) & Cmp:
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

def String.eq.fin(r: (String & String) & Cmp) -> Bool:
  ((a2, b2), c) = r
  Cmp.is_eq(c)

def String.eq(a: String, b: String) -> Bool:
  String.eq.fin(String.cmp(a, b))

# Text
# ----

def U32.read.dig.if(x: U32, ok: Bool) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      Some{U32.sub(x, 48)}
    case False{}:
      None{}

def U32.read.dig(c: Char) -> Maybe<&2, U32>:
  match c:
    case Chr{x}:
      +x2 = x
      U32.read.dig.if(x2, Bool.and(U32.is_le(48, x2), U32.is_le(x2, 57)))

def Nat.show.put(qr: Nat & Nat) -> Char & Nat:
  (q, r) = qr
  (Chr{U32.from_nat(Nat.add(48n, r))}, q)

def Nat.show.step(n: Nat) -> Char & Nat:
  Nat.show.put(Nat.divmod(n, 10n))

law Nat.show.go:
  for f   : Nat
  for n   : Nat
  for acc : String
  String

def Nat.show.fin(g: Nat, acc: String, dq: Char & Nat) -> String:
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

def Nat.show(+n: Nat) -> String:
  Nat.show.fin(n, SNil{}, Nat.show.step(n))

law Nat.read.go:
  for s   : String
  for acc : Nat
  Maybe<&2, Nat>

def Nat.read.fin(t: String, acc: Nat, d: Maybe<&2, U32>) -> Maybe<&2, Nat>:
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

def Nat.read(s: String) -> Maybe<&2, Nat>:
  match s:
    case SNil{}:
      None{}
    case SCon{h, t}:
      Nat.read.go(SCon{h, t}, 0n)

law U32.show.go:
  for f   : Nat
  for +n  : U32
  for acc : String
  String

def U32.show.fin(g: Nat, acc: String, +n: U32, z: Bool) -> String:
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

def U32.show.if(a: U32, z: Bool) -> String:
  match z:
    case True{}:
      SCon{Chr{48}, SNil{}}
    case False{}:
      U32.show.go(10n, a, SNil{})

def U32.show(+a: U32) -> String:
  U32.show.if(a, U32.is_zero(a))

law U32.read.go:
  for s   : String
  for acc : U32
  Maybe<&2, U32>

def U32.read.fin(t: String, acc: U32, d: Maybe<&2, U32>) -> Maybe<&2, U32>:
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

def U32.read(s: String) -> Maybe<&2, U32>:
  match s:
    case SNil{}:
      None{}
    case SCon{h, t}:
      U32.read.go(SCon{h, t}, 0)

# Array
# -----

def Array.size.node(-T: Type, ys: Array<T>, r: Array<T> & U32) ->
  Array<T> & U32:
  (xs2, n) = r
  (ANode{xs2, ys}, U32.shl(n))

def Array.size(-T: Type, a: Array<T>) -> Array<T> & U32:
  match a:
    case ALeaf{x}:
      (ALeaf{x}, 1)
    case ANode{xs, ys}:
      Array.size.node(T, ys, Array.size(T, xs))

def Array.swap.lo(-T: Type, ys: Array<T>, r: Array<T> & T) -> Array<T> & T:
  (nxs, old) = r
  (ANode{nxs, ys}, old)

def Array.swap.hi(-T: Type, xs: Array<T>, r: Array<T> & T) -> Array<T> & T:
  (nys, old) = r
  (ANode{xs, nys}, old)

law Array.swap.go:
  for -T: Type
  for  a: Array<T>
  for  n: U32
  for +i: U32
  for  v: T
  Array<T> & T

def Array.swap.if(
  -T: Type, xs: Array<T>, ys: Array<T>, +h: U32, i: U32, v: T, z: Bool
) -> Array<T> & T:
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

def Array.swap.at(-T: Type, i: U32, v: T, an: Array<T> & U32) -> Array<T> & T:
  (a, n) = an
  +m = n
  Array.swap.go(T, a, m, U32.and(i, U32.sub(m, 1)), v)

def Array.swap(-T: Type, a: Array<T>, +i: U32, v: T) -> Array<T> & T:
  Array.swap.at(T, i, v, Array.size(T, a))

def Array.clone.node(
  cx: Array<U32> & Array<U32>, cy: Array<U32> & Array<U32>
) -> Array<U32> & Array<U32>:
  (xa, xb) = cx
  (ya, yb) = cy
  (ANode{xa, ya}, ANode{xb, yb})

def Array.clone(a: Array<U32>) -> Array<U32> & Array<U32>:
  match a:
    case ALeaf{x}:
      +x2 = x
      (ALeaf{x2}, ALeaf{x2})
    case ANode{xs, ys}:
      Array.clone.node(Array.clone(xs), Array.clone(ys))

def Array.new(-T: Data, +d: Nat, +v: T) -> Array<T>:
  match d:
    case 0n:
      ALeaf{v}
    case 1n+p:
      ANode{Array.new(T, p, v), Array.new(T, p, v)}

def Array.set.fin(-T: Type, r: Array<T> & T) -> Array<T>:
  (na, old) = r
  na

def Array.set(-T: Type, a: Array<T>, i: U32, v: T) -> Array<T>:
  Array.set.fin(T, Array.swap(T, a, i, v))

law Array.get.go:
  for -T: Data
  for  a: Array<T>
  for  n: U32
  for +i: U32
  Array<T> & T

def Array.get.if(
  -T: Data, xs: Array<T>, ys: Array<T>, +h: U32, i: U32, z: Bool
) -> Array<T> & T:
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

def Array.get.at(-T: Data, i: U32, an: Array<T> & U32) -> Array<T> & T:
  (a, n) = an
  +m = n
  Array.get.go(T, a, m, U32.and(i, U32.sub(m, 1)))

def Array.get(-T: Data, a: Array<T>, +i: U32) -> Array<T> & T:
  Array.get.at(T, i, Array.size(T, a))

# Map
# ---

def Map.bit.u(x: U32, k: Nat) -> Bool:
  U32.is_ne(U32.and(U32.shrn(x, k), 1), 0)

def Map.bit.chr(c: Char, off: Nat) -> Char & Bool:
  match c:
    case Chr{x}:
      match off:
        case 0n:
          (Chr{x}, True{})
        case 1n+b:
          +x2 = x
          (Chr{x2}, Map.bit.u(x2, Nat.sub(31n, b)))

def Map.bit.go.chr(t: String, r: Char & Bool) -> String & Bool:
  (c2, b) = r
  (SCon{c2, t}, b)

def Map.bit.go.rec(c: Char, r: String & Bool) -> String & Bool:
  (t2, b) = r
  (SCon{c, t2}, b)

def Map.bit.go(key: String, ci: Nat, off: Nat) -> String & Bool:
  match key:
    case SNil{}:
      (SNil{}, False{})
    case SCon{c, t}:
      match ci:
        case 0n:
          Map.bit.go.chr(t, Map.bit.chr(c, off))
        case 1n+j:
          Map.bit.go.rec(c, Map.bit.go(t, j, off))

def Map.bit.at(key: String, co: Nat & Nat) -> String & Bool:
  (ci, off) = co
  Map.bit.go(key, ci, off)

def Map.bit(key: String, pos: Nat) -> String & Bool:
  Map.bit.at(key, Nat.divmod(pos, 33n))

law Map.msb.u:
  for n: Nat
  for x: U32
  Nat

def Map.msb.u.if(p: Nat, x2: U32, z: Bool) -> Nat:
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

def Map.diff.chr(x: U32) -> Nat:
  Nat.sub(33n, Map.msb.u(32n, x))

def Map.diff.step(x: Char, y: Char) -> Nat & Bool:
  match x y:
    case Chr{cx} Chr{cy}:
      +cx2 = cx
      +cy2 = cy
      (Map.diff.chr(U32.xor(cx2, cy2)), U32.is_eq(cx2, cy2))

law Map.diff:
  for a: String
  for b: String
  Nat

def Map.diff.fin(xt: String, yt: String, rc: Nat & Bool) -> Nat:
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

def Map.new(a, -V: Kind(a)) -> Map<a, V>:
  MTip{}

law Map.put:
  for -a  : Quant
  for -V  : Kind(a)
  for m   : Map<a, V>
  for key : String
  for x   : V
  Map<a, V>

def Map.put.bit(
  a, -V: Kind(a), x: V, p2: Nat, lo: Map<a, V>, hi: Map<a, V>, kb: String & Bool
) -> Map<a, V>:
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

def Map.ins.splice.bit(
  a, -V: Kind(a), x: V, rest: Map<a, V>, pb: Nat, kb: String & Bool
) -> Map<a, V>:
  (key2, b) = kb
  match b:
    case False{}:
      MNode{pb, MLeaf{key2, x}, rest}
    case True{}:
      MNode{pb, rest, MLeaf{key2, x}}

def Map.ins.splice(
  a, -V: Kind(a), +p: Nat, key: String, x: V, rest: Map<a, V>
) -> Map<a, V>:
  Map.ins.splice.bit(a, V, x, rest, p, Map.bit(key, p))

law Map.ins:
  for -a  : Quant
  for -V  : Kind(a)
  for m   : Map<a, V>
  for key : String
  for x   : V
  for +p  : Nat
  Map<a, V>

def Map.ins.deep(
  a, -V: Kind(a), x: V, lo: Map<a, V>, hi: Map<a, V>, pb: Nat, qb: Nat,
  kb: String & Bool
) -> Map<a, V>:
  (key2, b) = kb
  match b:
    case False{}:
      MNode{qb, Map.ins(a, V, lo, key2, x, pb), hi}
    case True{}:
      MNode{qb, lo, Map.ins(a, V, hi, key2, x, pb)}

def Map.ins.if(
  a, -V: Kind(a), key: String, x: V, lo: Map<a, V>, hi: Map<a, V>, +p2: Nat,
  pb: Nat, t: Bool
) -> Map<a, V>:
  match t:
    case False{}:
      Map.ins.splice(a, V, pb, key, x, MNode{p2, lo, hi})
    case True{}:
      Map.ins.deep(a, V, x, lo, hi, pb, p2, Map.bit(key, p2))

def Map.ins(a, V, m, key, x, p):
  match m:
    case MTip{}:
      MLeaf{key, x}
    case MLeaf{k, v}:
      Map.ins.splice(a, V, p, key, x, MLeaf{k, v})
    case MNode{pos, lo, hi}:
      +pos2 = pos
      Map.ins.if(a, V, key, x, lo, hi, pos2, p, Nat.is_lt(pos2, p))

def Map.seek.lo(
  a, -V: Kind(a), p2: Nat, hi: Map<a, V>,
  r0: (Map<a, V> & String) & Maybe<&2, String>
) -> (Map<a, V> & String) & Maybe<&2, String>:
  ((lo2, key3), r) = r0
  ((MNode{p2, lo2, hi}, key3), r)

def Map.seek.hi(
  a, -V: Kind(a), p2: Nat, lo: Map<a, V>,
  r0: (Map<a, V> & String) & Maybe<&2, String>
) -> (Map<a, V> & String) & Maybe<&2, String>:
  ((hi2, key3), r) = r0
  ((MNode{p2, lo, hi2}, key3), r)

law Map.seek:
  for -a  : Quant
  for -V  : Kind(a)
  for m   : Map<a, V>
  for key : String
  (Map<a, V> & String) & Maybe<&2, String>

def Map.seek.bit(
  a, -V: Kind(a), lo: Map<a, V>, hi: Map<a, V>, p2: Nat, kb: String & Bool
) -> (Map<a, V> & String) & Maybe<&2, String>:
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

def Map.set.fin.go(
  a, -V: Kind(a), m: Map<a, V>, key: String, x: V, r: (String & String) & Cmp
) -> Map<a, V>:
  ((keyb2, k2), c) = r
  match c:
    case LT{}:
      Map.ins(a, V, m, key, x, Map.diff(keyb2, k2))
    case EQ{}:
      Map.put(a, V, m, key, x)
    case GT{}:
      Map.ins(a, V, m, key, x, Map.diff(keyb2, k2))

def Map.set.fin(
  a, -V: Kind(a), m: Map<a, V>, key: String, x: V, keyb: String, k: String
) -> Map<a, V>:
  Map.set.fin.go(a, V, m, key, x, String.cmp(keyb, k))

def Map.set.go(
  a, -V: Kind(a), x: V, r: (Map<a, V> & String) & Maybe<&2, String>
) -> Map<a, V>:
  ((m2, key2), found) = r
  match found:
    case None{}:
      MLeaf{key2, x}
    case Some{k}:
      +ka = {key2 : String}
      Map.set.fin(a, V, m2, ka, x, ka, k)

def Map.set(a, -V: Kind(a), m: Map<a, V>, key: String, x: V) -> Map<a, V>:
  Map.set.go(a, V, x, Map.seek(a, V, m, key))

def Map.set.kv(
  a, -V: Kind(a), m: Map<a, V>, kv: Sigma<&2, a, String, _ => V>
) -> Map<a, V>:
  (k, v) = kv
  Map.set(a, V, m, k, v)

def Map.has.leaf(a, -V: Kind(a), v: V, r: (String & String) & Cmp) ->
  Map<a, V> & Bool:
  ((key2, k2), c) = r
  (MLeaf{k2, v}, Cmp.is_eq(c))

def Map.has.lo(a, -V: Kind(a), p2: Nat, hi: Map<a, V>, r0: Map<a, V> & Bool) ->
  Map<a, V> & Bool:
  (lo2, r) = r0
  (MNode{p2, lo2, hi}, r)

def Map.has.hi(a, -V: Kind(a), p2: Nat, lo: Map<a, V>, r0: Map<a, V> & Bool) ->
  Map<a, V> & Bool:
  (hi2, r) = r0
  (MNode{p2, lo, hi2}, r)

law Map.has:
  for -a  : Quant
  for -V  : Kind(a)
  for m   : Map<a, V>
  for key : String
  Map<a, V> & Bool

def Map.has.bit(
  a, -V: Kind(a), lo: Map<a, V>, hi: Map<a, V>, p2: Nat, kb: String & Bool
) -> Map<a, V> & Bool:
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

def Map.get.leaf(-V: Data, d: V, v: V, r: (String & String) & Cmp) ->
  Map<&2, V> & V:
  ((key2, k2), c) = r
  match c:
    case LT{}:
      (MLeaf{k2, v}, d)
    case EQ{}:
      +v2 = v
      (MLeaf{k2, v2}, v2)
    case GT{}:
      (MLeaf{k2, v}, d)

def Map.get.lo(-V: Data, p2: Nat, hi: Map<&2, V>, r0: Map<&2, V> & V) ->
  Map<&2, V> & V:
  (lo2, r) = r0
  (MNode{p2, lo2, hi}, r)

def Map.get.hi(-V: Data, p2: Nat, lo: Map<&2, V>, r0: Map<&2, V> & V) ->
  Map<&2, V> & V:
  (hi2, r) = r0
  (MNode{p2, lo, hi2}, r)

law Map.get:
  for -V  : Data
  for d   : V
  for m   : Map<&2, V>
  for key : String
  Map<&2, V> & V

def Map.get.bit(
  -V: Data, d: V, lo: Map<&2, V>, hi: Map<&2, V>, p2: Nat, kb: String & Bool
) -> Map<&2, V> & V:
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

def Map.pop.lo(
  a, -V: Kind(a), pos: Nat, lo: Map<a, V>, hi: Map<a, V>, r: Maybe<a, V>
) -> Map<a, V> & Maybe<a, V>:
  match lo:
    case MTip{}:
      (hi, r)
    case MLeaf{k, v}:
      (MNode{pos, MLeaf{k, v}, hi}, r)
    case MNode{p, a, b}:
      (MNode{pos, MNode{p, a, b}, hi}, r)

def Map.pop.hi(
  a, -V: Kind(a), pos: Nat, lo: Map<a, V>, hi: Map<a, V>, r: Maybe<a, V>
) -> Map<a, V> & Maybe<a, V>:
  match hi:
    case MTip{}:
      (lo, r)
    case MLeaf{k, v}:
      (MNode{pos, lo, MLeaf{k, v}}, r)
    case MNode{p, a, b}:
      (MNode{pos, lo, MNode{p, a, b}}, r)

def Map.pop.leaf(a, -V: Kind(a), v: V, r: (String & String) & Cmp) ->
  Map<a, V> & Maybe<a, V>:
  ((key2, k2), c) = r
  match c:
    case LT{}:
      (MLeaf{k2, v}, None{})
    case EQ{}:
      (MTip{}, Some{v})
    case GT{}:
      (MLeaf{k2, v}, None{})

def Map.pop.golo(
  a, -V: Kind(a), p2: Nat, hi: Map<a, V>, r0: Map<a, V> & Maybe<a, V>
) -> Map<a, V> & Maybe<a, V>:
  (lo2, r) = r0
  Map.pop.lo(a, V, p2, lo2, hi, r)

def Map.pop.gohi(
  a, -V: Kind(a), p2: Nat, lo: Map<a, V>, r0: Map<a, V> & Maybe<a, V>
) -> Map<a, V> & Maybe<a, V>:
  (hi2, r) = r0
  Map.pop.hi(a, V, p2, lo, hi2, r)

law Map.pop:
  for -a  : Quant
  for -V  : Kind(a)
  for m   : Map<a, V>
  for key : String
  Map<a, V> & Maybe<a, V>

def Map.pop.bit(
  a, -V: Kind(a), lo: Map<a, V>, hi: Map<a, V>, p2: Nat, kb: String & Bool
) -> Map<a, V> & Maybe<a, V>:
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

def Map.del.fin(a, -V: Kind(a), r: Map<a, V> & Maybe<a, V>) -> Map<a, V>:
  (m2, x) = r
  m2

def Map.del(a, -V: Kind(a), m: Map<a, V>, key: String) -> Map<a, V>:
  Map.del.fin(a, V, Map.pop(a, V, m, key))

def Map.to_list.go(
  a, -V: Kind(a), m: Map<a, V>, acc: List<a, Sigma<&2, a, String, _ => V>>
) -> List<a, Sigma<&2, a, String, _ => V>>:
  match m:
    case MTip{}:
      acc
    case MLeaf{k, v}:
      Con{(k, v), acc}
    case MNode{pos, lo, hi}:
      Map.to_list.go(a, V, lo, Map.to_list.go(a, V, hi, acc))

def Map.to_list(a, -V: Kind(a), m: Map<a, V>) ->
  List<a, Sigma<&2, a, String, _ => V>>:
  Map.to_list.go(a, V, m, Nil{})

def Map.keys.go(a, -V: Kind(a), m: Map<a, V>, acc: List<&2, String>) ->
  List<&2, String>:
  match m:
    case MTip{}:
      acc
    case MLeaf{k, v}:
      Con{k, acc}
    case MNode{pos, lo, hi}:
      Map.keys.go(a, V, lo, Map.keys.go(a, V, hi, acc))

def Map.keys(a, -V: Kind(a), m: Map<a, V>) -> List<&2, String>:
  Map.keys.go(a, V, m, Nil{})

def Map.from_list.go(
  a, -V: Kind(a), kvs: List<a, Sigma<&2, a, String, _ => V>>, m: Map<a, V>
) -> Map<a, V>:
  match kvs:
    case Nil{}:
      m
    case Con{kv, t}:
      Map.from_list.go(a, V, t, Map.set.kv(a, V, m, kv))

def Map.from_list(a, -V: Kind(a), kvs: List<a, Sigma<&2, a, String, _ => V>>) ->
  Map<a, V>:
  Map.from_list.go(a, V, kvs, MTip{})

def Map.union(a, -V: Kind(a), m: Map<a, V>, n: Map<a, V>) -> Map<a, V>:
  Map.from_list.go(a, V, Map.to_list(a, V, n), m)

# Set
# ---

def Set() -> Data:
  Map<&2, Unit>

def Set.new() -> Set():
  Map.new(&2, Unit)

def Set.add(s: Set(), key: String) -> Set():
  Map.set(&2, Unit, s, key, Unit{})

def Set.has(s: Set(), key: String) -> Set() & Bool:
  Map.has(&2, Unit, s, key)

def Set.del(s: Set(), key: String) -> Set():
  Map.del(&2, Unit, s, key)

def Set.union(a: Set(), b: Set()) -> Set():
  Map.union(&2, Unit, a, b)

# App
# ---

def App.next(
  -S: Type, window: Window, rest: Window -> S -> IO(Unit), next: Maybe<S>
) -> IO(Unit):
  match next:
    case None{}:
      Window.close(window)
    case Some{state}:
      rest(window, state)

def App.turn(
  -S: Type, shown: Window & Image & List<Event>,
  tick: List<Event> -> S -> IO(Maybe<S>), state: S,
  rest: Window -> S -> IO(Unit)
) -> IO(Unit):
  (window, image, events) = shown
  IO.bind(Maybe<S>, Unit, tick(events, state), App.next(S, window, rest))

def App.draw(
  -S: Type, window: Window, drawn: S & Image,
  tick: List<Event> -> S -> IO(Maybe<S>), rest: Window -> S -> IO(Unit)
) -> IO(Unit):
  (state, image) = drawn
  do IO<Unit>:
    shown : Window & Image & List<Event> <- Window.frame(window, image)
    App.turn(S, shown, tick, state, rest)

def App.step(
  -S: Type, app: App<S>, window: Window, state: S,
  rest: Window -> S -> IO(Unit)
) -> IO(Unit):
  App{view, tick} = app
  App.draw(S, window, view(state), tick, rest)

def App.loop(~S: Type, ~app: App<S>, fuel: Nat, window: Window, state: S) ->
  IO(Unit):
  match fuel:
    case 0n:
      Window.close(window)
    case 1n+f:
      App.step(S, app, window, state, w => s => App.loop(~S, ~app, f, w, s))

def App.run(
  ~S: Type, ~app: App<S>, title: String, width: U32, height: U32, state: S
) -> IO(Unit):
  do IO<Unit>:
    window : Window <- IO.try(Window, Window.open(title, width, height))
    App.loop(~S, ~app, U32.to_nat(4294967295), window, state)

def App.more(-S: Type, rest: S -> IO(Maybe<S>), next: Maybe<S>) ->
  IO(Maybe<S>):
  match next:
    case None{}:
      IO.pure(Maybe<S>, None{})
    case Some{state}:
      rest(state)

def App.fold(
  -S: Type, app: App<S>, events: List<Event>, state: S,
  rest: S -> IO(Maybe<S>)
) -> IO(Maybe<S>):
  App{view, tick} = app
  IO.bind(Maybe<S>, Maybe<S>, tick(events, state), App.more(S, rest))

def App.play(~S: Type, ~app: App<S>, frames: List<List<Event>>, state: S) ->
  IO(Maybe<S>):
  match frames:
    case Nil{}:
      IO.pure(Maybe<S>, Some{state})
    case Con{events, rest}:
      App.fold(S, app, events, state, s => App.play(~S, ~app, rest, s))
