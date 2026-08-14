# Base
# ====

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

type Either<A: Type, B: Type>:
  Inl{value: A}
  Inr{value: B}

type Sigma<-A: Type, -B: @-x: A -> Type>:
  Tuple{fst: A, snd: B(fst)}

def Pair(-A: Type, -B: Type) -> Type:
  Sigma<A, _ => B>

type Nat:
  Zero{}
  Succ{pred: Nat}

type Maybe<A: Type>:
  None{}
  Some{value: A}

type Result<E: Type, A: Type>:
  Fail{error: E}
  Done{value: A}

type List<A: Type>:
  Nil{}
  Con{head: A, tail: List<A>}

type Array<T: Type>:
  ALeaf{value: T}
  ANode{xs: Array<T>, ys: Array<T>}

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

# Effects
# -------

type Fiber<A: Type>:
  Fiber{slot: U32, gen: U32}

type File:
  File{slot: U32, gen: U32}

type Socket:
  Socket{slot: U32, gen: U32}

type Listener:
  Listener{slot: U32, gen: U32}

type Sender<A: Type>:
  Sender{slot: U32, gen: U32}

type Receiver<A: Type>:
  Receiver{slot: U32, gen: U32}

type IO.OP<R: Type>:
  Emit{value: R}
  Halt{code: U32, message: String}
  Fork{-A: Type, body: IO.OP<A>, cont: Fiber<A> -> IO.OP<R>}
  Join{-A: Type, fiber: Fiber<A>, cont: A -> IO.OP<R>}
  Kill{-A: Type, fiber: Fiber<A>, cont: Unit -> IO.OP<R>}
  Race{-A: Type, left: IO.OP<A>, right: IO.OP<A>, cont: A -> IO.OP<R>}
  Task{body: IO.OP<Unit>, cont: Unit -> IO.OP<R>}
  CNew{-A: Type, capacity: Nat, cont: Sender<A> & Receiver<A> -> IO.OP<R>}
  Send{-A: Type, sender: Sender<A>, value: A, cont: Result<A, Sender<A>> -> IO.OP<R>}
  Recv{-A: Type, receiver: Receiver<A>, cont: Result<Unit, A & Receiver<A>> -> IO.OP<R>}
  Shut{-A: Type, sender: Sender<A>, cont: Unit -> IO.OP<R>}

def IO(-A: Type) -> Type:
  @-R: Type ->
  @k: (A -> IO.OP<R>) ->
  IO.OP<R>

# Theorems
# --------

def Copy(-A: Type, -x: A) -> Type:
  &y: A -> {x == y : A}

# Equal
# =====

def Equal.cong(-A: Type, -B: Type, -f: A -> B, -a: A, -b: A, e: {a == b : A}) -> {f(a) == f(b) : B}:
  %e : {f(a) == f(_) : B}; {==}

def Equal.sym(-A: Type, -a: A, -b: A, e: {a == b : A}) -> {b == a : A}:
  %e : {_ == a : A}; {==}

def Equal.trans(-A: Type, -a: A, -b: A, -c: A, ab: {a == b : A}, bc: {b == c : A}) -> {a == c : A}:
  %bc : {a == _ : A}; ab

def Equal.copy(-A: Type, -a: A, -b: A, e: {a == b : A}) -> Copy({a == b : A}, e) & Copy({a == b : A}, e):
  %x@e : Copy({a == _ : A}, x) & Copy({a == _ : A}, x);
  (({==}, {==}), ({==}, {==}))

# Empty
# =====

def Empty.absurd(-A: Type, e: Empty) -> A:
  match e:

# Bool
# ====

def B0() -> Bool:
  False{}

def B1() -> Bool:
  True{}

def Bool.if(-P: Type, b: Bool, t: P, f: P) -> P:
  match b:
    case False{}:
      f
    case True{}:
      t

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

def Bool.copy(b: Bool) -> Copy(Bool, b) & Copy(Bool, b):
  match b:
    case False{}:
      ((False{}, {==}), (False{}, {==}))
    case True{}:
      ((True{}, {==}), (True{}, {==}))

# (sum, carry) of a + b + c
def Bool.full_add(a: Bool, b: Bool, c: Bool) -> Bool & Bool:
  match a b c:
    case False{} False{} False{}:
      (B0(), B0())
    case False{} False{} True{}:
      (B1(), B0())
    case False{} True{} False{}:
      (B1(), B0())
    case False{} True{} True{}:
      (B0(), B1())
    case True{} False{} False{}:
      (B1(), B0())
    case True{} False{} True{}:
      (B0(), B1())
    case True{} True{} False{}:
      (B0(), B1())
    case True{} True{} True{}:
      (B1(), B1())

# Cmp
# ===

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

# Either
# ======

def Either.is_inl(-A: Type, -B: Type, e: A | B) -> Bool:
  match e:
    case Inl{x}:
      True{}
    case Inr{y}:
      False{}

def Either.is_inr(-A: Type, -B: Type, e: A | B) -> Bool:
  match e:
    case Inl{x}:
      False{}
    case Inr{y}:
      True{}

# Sigma
# =====

def Sigma.fst(-A: Type, -B: @-x: A -> Type, p: Sigma<A, B>) -> A:
  match p:
    case (x, y):
      x

def Sigma.snd(-A: Type, -B: @-x: A -> Type, p: Sigma<A, B>) -> B(Sigma.fst(A, B, p)):
  match p:
    case (x, y):
      y

# Pair
# ====

def Pair.fst(-A: Type, -B: Type, p: A & B) -> A:
  match p:
    case (x, y):
      x

def Pair.snd(-A: Type, -B: Type, p: A & B) -> B:
  match p:
    case (x, y):
      y

def Pair.swap(-A: Type, -B: Type, p: A & B) -> B & A:
  match p:
    case (x, y):
      (y, x)

# Nat
# ===

def Nat.copy(n: Nat) -> Copy(Nat, n) & Copy(Nat, n):
  match n:
    case 0n:
      ((0n, {==}), (0n, {==}))
    case 1n+p:
      ((a, ea), (b, eb)) = Nat.copy(p)
      pa = Equal.cong(Nat, Nat, x => 1n+x, p, a, ea)
      pb = Equal.cong(Nat, Nat, x => 1n+x, p, b, eb)
      ((1n+a, pa), (1n+b, pb))

def Nat.is_zero(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      False{}

def Nat.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

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

def Nat.mul(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      0n
    case 1n+p:
      ((b1, e1), (b2, e2)) = Nat.copy(b)
      Nat.add(b1, Nat.mul(p, b2))

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

def Nat.div(a: Nat, b: Nat) -> Nat:
  match Nat.divmod(a, b):
    case (q, r):
      q

def Nat.mod(a: Nat, b: Nat) -> Nat:
  match Nat.divmod(a, b):
    case (q, r):
      r

def Nat.min(a: Nat, b: Nat) -> Nat:
  match a b:
    case 0n y:
      0n
    case 1n+ap 0n:
      0n
    case 1n+ap 1n+bp:
      1n+Nat.min(ap, bp)

def Nat.max(a: Nat, b: Nat) -> Nat:
  match a b:
    case 0n y:
      y
    case 1n+ap 0n:
      1n+ap
    case 1n+ap 1n+bp:
      1n+Nat.max(ap, bp)

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

def Nat.is_eq(a: Nat, b: Nat) -> Bool:
  Cmp.is_eq(Nat.cmp(a, b))

def Nat.is_ne(a: Nat, b: Nat) -> Bool:
  Bool.not(Cmp.is_eq(Nat.cmp(a, b)))

def Nat.is_lt(a: Nat, b: Nat) -> Bool:
  Cmp.is_lt(Nat.cmp(a, b))

def Nat.is_le(a: Nat, b: Nat) -> Bool:
  Cmp.is_le(Nat.cmp(a, b))

def Nat.is_gt(a: Nat, b: Nat) -> Bool:
  Cmp.is_gt(Nat.cmp(a, b))

def Nat.is_ge(a: Nat, b: Nat) -> Bool:
  Cmp.is_ge(Nat.cmp(a, b))

def Nat.pow2(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+p:
      Nat.double(Nat.pow2(p))

def Nat.bits(m: Nat) -> Bool & Nat:
  match m:
    case 0n:
      (B0(), 0n)
    case 1n:
      (B1(), 0n)
    case 2n+r:
      (b, h) = Nat.bits(r)
      (b, 1n+h)

# Maybe
# =====

def Maybe.pure(-A: Type, x: A) -> Maybe<A>:
  Some{x}

def Maybe.bind(-A: Type, -B: Type, m: Maybe<A>, f: A -> Maybe<B>) -> Maybe<B>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      f(x)

def Maybe.is_none(-A: Type, m: Maybe<A>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      False{}

def Maybe.is_some(-A: Type, m: Maybe<A>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

def Maybe.default(-A: Type, m: Maybe<A>, d: A) -> A:
  match m:
    case None{}:
      d
    case Some{x}:
      x

# Result
# ======

def Result.pure(-E: Type, -A: Type, x: A) -> Result<E, A>:
  Done{x}

def Result.fail(-E: Type, -A: Type, e: E) -> Result<E, A>:
  Fail{e}

def Result.bind(-E: Type, -A: Type, -B: Type, r: Result<E, A>, f: A -> Result<E, B>) -> Result<E, B>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      f(x)

def Result.is_fail(-E: Type, -A: Type, r: Result<E, A>) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{x}:
      False{}

def Result.is_done(-E: Type, -A: Type, r: Result<E, A>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{x}:
      True{}

# List
# ====

def List.length(-A: Type, xs: List<A>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+List.length(A, t)

def List.append(-A: Type, xs: List<A>, ys: List<A>) -> List<A>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, List.append(A, t, ys)}

def List.reverse.go(-A: Type, xs: List<A>, acc: List<A>) -> List<A>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      List.reverse.go(A, t, Con{h, acc})

def List.reverse(-A: Type, xs: List<A>) -> List<A>:
  List.reverse.go(A, xs, Nil{})

def List.take(-A: Type, n: Nat, xs: List<A>) -> List<A>:
  match n xs:
    case 0n ys:
      Nil{}
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{h, t}:
      Con{h, List.take(A, p, t)}

def List.drop(-A: Type, n: Nat, xs: List<A>) -> List<A>:
  match n xs:
    case 0n ys:
      ys
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{h, t}:
      List.drop(A, p, t)

# Word
# ====

def Word.cast(-m: Nat, -n: Nat, e: {m == n : Nat}, w: Word(m)) -> Word(n):
  %e : Word(_); w

def Word.zero(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{B0(), Word.zero(p)}

def Word.copy(n: Nat, w: Word(n)) -> Copy(Word(n), w) & Copy(Word(n), w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          ((WNil{}, {==}), (WNil{}, {==}))
    case 1n+p:
      match w:
        case WCon{False{}, rest}:
          ((r1, e1), (r2, e2)) = Word.copy(p, rest)
          pa = Equal.cong(Word(p), Word(1n+p), y => WCon{B0(), y}, rest, r1, e1)
          pb = Equal.cong(Word(p), Word(1n+p), y => WCon{B0(), y}, rest, r2, e2)
          ((WCon{B0(), r1}, pa), (WCon{B0(), r2}, pb))
        case WCon{True{}, rest}:
          ((r1, e1), (r2, e2)) = Word.copy(p, rest)
          pa = Equal.cong(Word(p), Word(1n+p), y => WCon{B1(), y}, rest, r1, e1)
          pb = Equal.cong(Word(p), Word(1n+p), y => WCon{B1(), y}, rest, r2, e2)
          ((WCon{B1(), r1}, pa), (WCon{B1(), r2}, pb))

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
          WCon{B0(), Word.shl.put(p, b, t)}

def Word.shr.pad(n: Nat, w: Word(n)) -> Word(1n+n):
  match n:
    case 0n:
      WCon{B0(), w}
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

def Word.cmp(n: Nat, a: Word(n), b: Word(n)) -> Cmp:
  match n:
    case 0n:
      EQ{}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          match Word.cmp(p, at, bt):
            case LT{}:
              LT{}
            case EQ{}:
              Bool.cmp(ab, bb)
            case GT{}:
              GT{}

def Word.is_eq(n: Nat, a: Word(n), b: Word(n)) -> Bool:
  Cmp.is_eq(Word.cmp(n, a, b))

def Word.is_ne(n: Nat, a: Word(n), b: Word(n)) -> Bool:
  Bool.not(Cmp.is_eq(Word.cmp(n, a, b)))

def Word.is_lt(n: Nat, a: Word(n), b: Word(n)) -> Bool:
  Cmp.is_lt(Word.cmp(n, a, b))

def Word.is_le(n: Nat, a: Word(n), b: Word(n)) -> Bool:
  Cmp.is_le(Word.cmp(n, a, b))

def Word.is_gt(n: Nat, a: Word(n), b: Word(n)) -> Bool:
  Cmp.is_gt(Word.cmp(n, a, b))

def Word.is_ge(n: Nat, a: Word(n), b: Word(n)) -> Bool:
  Cmp.is_ge(Word.cmp(n, a, b))

def Word.inc(n: Nat, w: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          WCon{B1(), t}
        case WCon{True{}, t}:
          WCon{B0(), Word.inc(p, t)}

def Word.adc(n: Nat, a: Word(n), b: Word(n), f: Bool, c: Bool) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match a b f:
        case WCon{ab, at} WCon{bb, bt} False{}:
          (s, k) = Bool.full_add(ab, bb, c)
          WCon{s, Word.adc(p, at, bt, B0(), k)}
        case WCon{ab, at} WCon{bb, bt} True{}:
          (s, k) = Bool.full_add(ab, Bool.not(bb), c)
          WCon{s, Word.adc(p, at, bt, B1(), k)}

def Word.add(n: Nat, a: Word(n), b: Word(n)) -> Word(n):
  Word.adc(n, a, b, B0(), B0())

def Word.sub(n: Nat, a: Word(n), b: Word(n)) -> Word(n):
  Word.adc(n, a, b, B1(), B1())

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

def Word.mul.split(n: Nat, w: Word(1n+n)) ->
  &i: Nat -> &j: Nat ->
  {n == i : Nat} & {n == j : Nat} &
  Word(n) & Word(1n+n):
  match n w:
    case 0n WCon{b, t}:
      (0n, 0n, {==}, {==}, WNil{}, WCon{b, t})
    case 1n+p WCon{False{}, t}:
      (i, j, ei, ej, lo, hi) = Word.mul.split(p, t)
      ci = Equal.cong(Nat, Nat, x => 1n+x, p, i, ei)
      cj = Equal.cong(Nat, Nat, x => 1n+x, p, j, ej)
      (1n+i, 1n+j, ci, cj, WCon{B0(), lo}, WCon{B0(), hi})
    case 1n+p WCon{True{}, t}:
      (i, j, ei, ej, lo, hi) = Word.mul.split(p, t)
      ci = Equal.cong(Nat, Nat, x => 1n+x, p, i, ei)
      cj = Equal.cong(Nat, Nat, x => 1n+x, p, j, ej)
      (1n+i, 1n+j, ci, cj, WCon{B1(), lo}, WCon{B1(), hi})

def Word.mul(n: Nat, a: Word(n), b: Word(n)) -> Word(n):
  match n a:
    case 0n WNil{}:
      WNil{}
    case 1n+p WCon{False{}, at}:
      (i, j, ei, ej, lo, hi) = Word.mul.split(p, b)
      f = {%Equal.sym(Nat, p, i, ei) : Word(_) -> Word(_) -> Word(_); x => y => Word.mul(i, x, y) : Word(p) -> Word(p) -> Word(p)}
      WCon{B0(), f(at, lo)}
    case 1n+p WCon{True{}, at}:
      (i, j, ei, ej, lo, hi) = Word.mul.split(p, b)
      f = {%Equal.sym(Nat, p, i, ei) : Word(_) -> Word(_) -> Word(_); x => y => Word.mul(i, x, y) : Word(p) -> Word(p) -> Word(p)}
      r = f(at, lo)
      g = {%Equal.sym(Nat, p, j, ej) : Word(1n+_) -> Word(_) -> Word(1n+_); h => x => Word.add(1n+j, h, WCon{B0(), x}) : Word(1n+p) -> Word(p) -> Word(1n+p)}
      g(hi, r)

# U32
# ===

def U32.zero() -> U32:
  U32{Word.zero(32n)}

def U32.one() -> U32:
  U32{Word.inc(32n, Word.zero(32n))}

def U32.copy(u: U32) -> Copy(U32, u) & Copy(U32, u):
  match u:
    case U32{w}:
      ((w1, e1), (w2, e2)) = Word.copy(32n, w)
      p1 = Equal.cong(Word(32n), U32, x => U32{x}, w, w1, e1)
      p2 = Equal.cong(Word(32n), U32, x => U32{x}, w, w2, e2)
      ((U32{w1}, p1), (U32{w2}, p2))

def U32.inc(a: U32) -> U32:
  match a:
    case U32{x}:
      U32{Word.inc(32n, x)}

def U32.add(a: U32, b: U32) -> U32:
  match a b:
    case U32{x} U32{y}:
      U32{Word.add(32n, x, y)}

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

def U32.shln(n: Nat, a: U32) -> U32:
  match n:
    case 0n:
      a
    case 1n+p:
      U32.shln(p, U32.shl(a))

def U32.shrn(n: Nat, a: U32) -> U32:
  match n:
    case 0n:
      a
    case 1n+p:
      U32.shrn(p, U32.shr(a))

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

def U32.div(a: U32, b: U32) -> U32:
  ((b1, e1), (b2, e2)) = U32.copy(b)
  match U32.is_zero(b1):
    case True{}:
      U32.zero()
    case False{}:
      (q, r) = Nat.divmod(U32.to_nat(a), U32.to_nat(b2))
      U32.from_nat(q)

def U32.mod(a: U32, b: U32) -> U32:
  ((b1, e1), (b2, e2)) = U32.copy(b)
  match U32.is_zero(b1):
    case True{}:
      U32.zero()
    case False{}:
      (q, r) = Nat.divmod(U32.to_nat(a), U32.to_nat(b2))
      U32.from_nat(r)

# String
# ======

def String.append(a: String, b: String) -> String:
  match a:
    case SNil{}:
      b
    case SCon{h, t}:
      SCon{h, String.append(t, b)}
# Array
# =====
#
# A perfect binary tree of cells; the runtime runs it as one flat
# block. swap is the one array method: it routes by the index's low
# bit, one bit per level, so no size rides along, and answers the
# remaining array FIRST.

def Array.swap(-T: Type, a: Array<T>, i: U32, v: T) -> Array<T> & T:
  match a:
    case ALeaf{x}:
      (ALeaf{v}, x)
    case ANode{xs, ys}:
      ((i1, e1), (i2, e2)) = U32.copy(i)
      match U32.is_zero(U32.and(i1, U32.one())):
        case True{}:
          (nxs, old) = Array.swap(T, xs, U32.shr(i2), v)
          (ANode{nxs, ys}, old)
        case False{}:
          (nys, old) = Array.swap(T, ys, U32.shr(i2), v)
          (ANode{xs, nys}, old)
