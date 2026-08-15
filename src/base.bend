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

assert Equal.cong:
  forall -A: Type
  forall -B: Type
  forall -f: A -> B
  forall -a: A
  forall -b: A
  forall  e: {a == b : A}
  {f(a) == f(b) : B}

def Equal.cong(A, B, f, a, b, e):
  %e : {f(a) == f(_) : B}; {==}

assert Equal.sym:
  forall -A: Type
  forall -a: A
  forall -b: A
  forall e: {a == b : A}
  {b == a : A}

def Equal.sym(A, a, b, e):
  %e : {_ == a : A}; {==}

assert Equal.trans:
  forall -A: Type
  forall -a: A
  forall -b: A
  forall -c: A
  forall ab: {a == b : A}
  forall bc: {b == c : A}
  {a == c : A}

def Equal.trans(A, a, b, c, ab, bc):
  %bc : {a == _ : A}; ab

assert Equal.copy:
  forall -A: Type
  forall -a: A
  forall -b: A
  forall  e: {a == b : A}
  Copy({a == b : A}, e) & Copy({a == b : A}, e)

def Equal.copy(A, a, b, e):
  %x@e : Copy({a == _ : A}, x) & Copy({a == _ : A}, x);
  (({==}, {==}), ({==}, {==}))

# Empty
# =====

assert Empty.absurd:
  forall -A: Type
  forall  e: Empty
  A

def Empty.absurd(A, e):
  match e:

# Bool
# ====

assert B0:
  Bool

def B0():
  False{}

assert B1:
  Bool

def B1():
  True{}

assert Bool.if:
  forall -P: Type
  forall  b: Bool
  forall  t: P
  forall  f: P
  P

def Bool.if(P, b, t, f):
  match b:
    case False{}:
      f
    case True{}:
      t

assert Bool.not:
  forall b: Bool
  Bool

def Bool.not(b):
  match b:
    case False{}:
      True{}
    case True{}:
      False{}

assert Bool.and:
  forall a: Bool
  forall b: Bool
  Bool

def Bool.and(a, b):
  match a:
    case False{}:
      False{}
    case True{}:
      b

assert Bool.or:
  forall a: Bool
  forall b: Bool
  Bool

def Bool.or(a, b):
  match a:
    case False{}:
      b
    case True{}:
      True{}

assert Bool.xor:
  forall a: Bool
  forall b: Bool
  Bool

def Bool.xor(a, b):
  match a:
    case False{}:
      b
    case True{}:
      Bool.not(b)

assert Bool.cmp:
  forall a: Bool
  forall b: Bool
  Cmp

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

assert Bool.copy:
  forall b: Bool
  Copy(Bool, b) & Copy(Bool, b)

def Bool.copy(b):
  match b:
    case False{}:
      ((False{}, {==}), (False{}, {==}))
    case True{}:
      ((True{}, {==}), (True{}, {==}))

# (sum, carry) of a + b + c
assert Bool.full_add:
  forall a: Bool
  forall b: Bool
  forall c: Bool
  Bool & Bool

def Bool.full_add(a, b, c):
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

assert Cmp.is_lt:
  forall c: Cmp
  Bool

def Cmp.is_lt(c):
  match c:
    case LT{}:
      True{}
    case EQ{}:
      False{}
    case GT{}:
      False{}

assert Cmp.is_eq:
  forall c: Cmp
  Bool

def Cmp.is_eq(c):
  match c:
    case LT{}:
      False{}
    case EQ{}:
      True{}
    case GT{}:
      False{}

assert Cmp.is_gt:
  forall c: Cmp
  Bool

def Cmp.is_gt(c):
  match c:
    case LT{}:
      False{}
    case EQ{}:
      False{}
    case GT{}:
      True{}

assert Cmp.is_le:
  forall c: Cmp
  Bool

def Cmp.is_le(c):
  match c:
    case LT{}:
      True{}
    case EQ{}:
      True{}
    case GT{}:
      False{}

assert Cmp.is_ge:
  forall c: Cmp
  Bool

def Cmp.is_ge(c):
  match c:
    case LT{}:
      False{}
    case EQ{}:
      True{}
    case GT{}:
      True{}

# Either
# ======

assert Either.is_inl:
  forall -A: Type
  forall -B: Type
  forall e: A | B
  Bool

def Either.is_inl(A, B, e):
  match e:
    case Inl{x}:
      True{}
    case Inr{y}:
      False{}

assert Either.is_inr:
  forall -A: Type
  forall -B: Type
  forall e: A | B
  Bool

def Either.is_inr(A, B, e):
  match e:
    case Inl{x}:
      False{}
    case Inr{y}:
      True{}

# Sigma
# =====

assert Sigma.fst:
  forall -A: Type
  forall -B: @-x: A -> Type
  forall p: Sigma<A, B>
  A

def Sigma.fst(A, B, p):
  match p:
    case (x, y):
      x

assert Sigma.snd:
  forall -A: Type
  forall -B: @-x: A -> Type
  forall p: Sigma<A, B>
  B(Sigma.fst(A, B, p))

def Sigma.snd(A, B, p):
  match p:
    case (x, y):
      y

# Pair
# ====

assert Pair.fst:
  forall -A: Type
  forall -B: Type
  forall p: A & B
  A

def Pair.fst(A, B, p):
  match p:
    case (x, y):
      x

assert Pair.snd:
  forall -A: Type
  forall -B: Type
  forall p: A & B
  B

def Pair.snd(A, B, p):
  match p:
    case (x, y):
      y

assert Pair.swap:
  forall -A: Type
  forall -B: Type
  forall p: A & B
  B & A

def Pair.swap(A, B, p):
  match p:
    case (x, y):
      (y, x)

# Nat
# ===

assert Nat.copy:
  forall n: Nat
  Copy(Nat, n) & Copy(Nat, n)

def Nat.copy(n):
  match n:
    case 0n:
      ((0n, {==}), (0n, {==}))
    case 1n+p:
      ((a, ea), (b, eb)) = Nat.copy(p)
      pa = Equal.cong(Nat, Nat, x => 1n+x, p, a, ea)
      pb = Equal.cong(Nat, Nat, x => 1n+x, p, b, eb)
      ((1n+a, pa), (1n+b, pb))

assert Nat.is_zero:
  forall n: Nat
  Bool

def Nat.is_zero(n):
  match n:
    case 0n:
      True{}
    case 1n+p:
      False{}

assert Nat.pred:
  forall n: Nat
  Nat

def Nat.pred(n):
  match n:
    case 0n:
      0n
    case 1n+p:
      p

assert Nat.double:
  forall n: Nat
  Nat

def Nat.double(n):
  match n:
    case 0n:
      0n
    case 1n+p:
      2n+Nat.double(p)

assert Nat.add:
  forall a: Nat
  forall b: Nat
  Nat

def Nat.add(a, b):
  match a:
    case 0n:
      b
    case 1n+p:
      1n+Nat.add(p, b)

assert Nat.sub:
  forall a: Nat
  forall b: Nat
  Nat

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

assert Nat.mul:
  forall a: Nat
  forall b: Nat
  Nat

def Nat.mul(a, b):
  match a:
    case 0n:
      0n
    case 1n+p:
      ((b1, e1), (b2, e2)) = Nat.copy(b)
      Nat.add(b1, Nat.mul(p, b2))

assert Nat.divmod.go:
  forall n: Nat
  forall m: Nat
  forall d: Nat
  forall r: Nat
  Nat & Nat

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

assert Nat.divmod:
  forall a: Nat
  forall b: Nat
  Nat & Nat

def Nat.divmod(a, b):
  match b:
    case 0n:
      (0n, a)
    case 1n+bp:
      Nat.divmod.go(a, bp, 0n, 0n)

assert Nat.div:
  forall a: Nat
  forall b: Nat
  Nat

def Nat.div(a, b):
  match Nat.divmod(a, b):
    case (q, r):
      q

assert Nat.mod:
  forall a: Nat
  forall b: Nat
  Nat

def Nat.mod(a, b):
  match Nat.divmod(a, b):
    case (q, r):
      r

assert Nat.min:
  forall a: Nat
  forall b: Nat
  Nat

def Nat.min(a, b):
  match a b:
    case 0n y:
      0n
    case 1n+ap 0n:
      0n
    case 1n+ap 1n+bp:
      1n+Nat.min(ap, bp)

assert Nat.max:
  forall a: Nat
  forall b: Nat
  Nat

def Nat.max(a, b):
  match a b:
    case 0n y:
      y
    case 1n+ap 0n:
      1n+ap
    case 1n+ap 1n+bp:
      1n+Nat.max(ap, bp)

assert Nat.cmp:
  forall a: Nat
  forall b: Nat
  Cmp

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

assert Nat.is_eq:
  forall a: Nat
  forall b: Nat
  Bool

def Nat.is_eq(a, b):
  Cmp.is_eq(Nat.cmp(a, b))

assert Nat.is_ne:
  forall a: Nat
  forall b: Nat
  Bool

def Nat.is_ne(a, b):
  Bool.not(Cmp.is_eq(Nat.cmp(a, b)))

assert Nat.is_lt:
  forall a: Nat
  forall b: Nat
  Bool

def Nat.is_lt(a, b):
  Cmp.is_lt(Nat.cmp(a, b))

assert Nat.is_le:
  forall a: Nat
  forall b: Nat
  Bool

def Nat.is_le(a, b):
  Cmp.is_le(Nat.cmp(a, b))

assert Nat.is_gt:
  forall a: Nat
  forall b: Nat
  Bool

def Nat.is_gt(a, b):
  Cmp.is_gt(Nat.cmp(a, b))

assert Nat.is_ge:
  forall a: Nat
  forall b: Nat
  Bool

def Nat.is_ge(a, b):
  Cmp.is_ge(Nat.cmp(a, b))

assert Nat.pow2:
  forall n: Nat
  Nat

def Nat.pow2(n):
  match n:
    case 0n:
      1n
    case 1n+p:
      Nat.double(Nat.pow2(p))

assert Nat.bits:
  forall m: Nat
  Bool & Nat

def Nat.bits(m):
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

assert Maybe.pure:
  forall -A: Type
  forall x: A
  Maybe<A>

def Maybe.pure(A, x):
  Some{x}

assert Maybe.bind:
  forall -A: Type
  forall -B: Type
  forall m: Maybe<A>
  forall f: A -> Maybe<B>
  Maybe<B>

def Maybe.bind(A, B, m, f):
  match m:
    case None{}:
      None{}
    case Some{x}:
      f(x)

assert Maybe.is_none:
  forall -A: Type
  forall m: Maybe<A>
  Bool

def Maybe.is_none(A, m):
  match m:
    case None{}:
      True{}
    case Some{x}:
      False{}

assert Maybe.is_some:
  forall -A: Type
  forall m: Maybe<A>
  Bool

def Maybe.is_some(A, m):
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

assert Maybe.default:
  forall -A: Type
  forall m: Maybe<A>
  forall d: A
  A

def Maybe.default(A, m, d):
  match m:
    case None{}:
      d
    case Some{x}:
      x

# Result
# ======

assert Result.pure:
  forall -E: Type
  forall -A: Type
  forall x: A
  Result<E, A>

def Result.pure(E, A, x):
  Done{x}

assert Result.fail:
  forall -E: Type
  forall -A: Type
  forall e: E
  Result<E, A>

def Result.fail(E, A, e):
  Fail{e}

assert Result.bind:
  forall -E: Type
  forall -A: Type
  forall -B: Type
  forall r: Result<E, A>
  forall f: A -> Result<E, B>
  Result<E, B>

def Result.bind(E, A, B, r, f):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      f(x)

assert Result.is_fail:
  forall -E: Type
  forall -A: Type
  forall r: Result<E, A>
  Bool

def Result.is_fail(E, A, r):
  match r:
    case Fail{e}:
      True{}
    case Done{x}:
      False{}

assert Result.is_done:
  forall -E: Type
  forall -A: Type
  forall r: Result<E, A>
  Bool

def Result.is_done(E, A, r):
  match r:
    case Fail{e}:
      False{}
    case Done{x}:
      True{}

# List
# ====

assert List.length:
  forall -A: Type
  forall xs: List<A>
  Nat

def List.length(A, xs):
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+List.length(A, t)

assert List.append:
  forall -A: Type
  forall xs: List<A>
  forall ys: List<A>
  List<A>

def List.append(A, xs, ys):
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, List.append(A, t, ys)}

assert List.reverse.go:
  forall -A: Type
  forall xs: List<A>
  forall acc: List<A>
  List<A>

def List.reverse.go(A, xs, acc):
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      List.reverse.go(A, t, Con{h, acc})

assert List.reverse:
  forall -A: Type
  forall xs: List<A>
  List<A>

def List.reverse(A, xs):
  List.reverse.go(A, xs, Nil{})

assert List.take:
  forall -A: Type
  forall n: Nat
  forall xs: List<A>
  List<A>

def List.take(A, n, xs):
  match n xs:
    case 0n ys:
      Nil{}
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{h, t}:
      Con{h, List.take(A, p, t)}

assert List.drop:
  forall -A: Type
  forall n: Nat
  forall xs: List<A>
  List<A>

def List.drop(A, n, xs):
  match n xs:
    case 0n ys:
      ys
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{h, t}:
      List.drop(A, p, t)

# Word
# ====

assert Word.cast:
  forall -m: Nat
  forall -n: Nat
  forall e: {m == n : Nat}
  forall w: Word(m)
  Word(n)

def Word.cast(m, n, e, w):
  %e : Word(_); w

assert Word.zero:
  forall n: Nat
  Word(n)

def Word.zero(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{B0(), Word.zero(p)}

assert Word.copy:
  forall n: Nat
  forall w: Word(n)
  Copy(Word(n), w) & Copy(Word(n), w)

def Word.copy(n, w):
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

assert Word.not:
  forall n: Nat
  forall w: Word(n)
  Word(n)

def Word.not(n, w):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{Bool.not(b), Word.not(p, t)}

assert Word.and:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  Word(n)

def Word.and(n, a, b):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          WCon{Bool.and(ab, bb), Word.and(p, at, bt)}

assert Word.or:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  Word(n)

def Word.or(n, a, b):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          WCon{Bool.or(ab, bb), Word.or(p, at, bt)}

assert Word.xor:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  Word(n)

def Word.xor(n, a, b):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          WCon{Bool.xor(ab, bb), Word.xor(p, at, bt)}

assert Word.shl.put:
  forall n: Nat
  forall c: Bool
  forall w: Word(n)
  Word(n)

def Word.shl.put(n, c, w):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{c, Word.shl.put(p, b, t)}

assert Word.shl:
  forall n: Nat
  forall w: Word(n)
  Word(n)

def Word.shl(n, w):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{B0(), Word.shl.put(p, b, t)}

assert Word.shr.pad:
  forall n: Nat
  forall w: Word(n)
  Word(1n+n)

def Word.shr.pad(n, w):
  match n:
    case 0n:
      WCon{B0(), w}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{b, Word.shr.pad(p, t)}

assert Word.shr:
  forall n: Nat
  forall w: Word(n)
  Word(n)

def Word.shr(n, w):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          Word.shr.pad(p, t)

assert Word.cmp:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  Cmp

def Word.cmp(n, a, b):
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

assert Word.is_eq:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  Bool

def Word.is_eq(n, a, b):
  Cmp.is_eq(Word.cmp(n, a, b))

assert Word.is_ne:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  Bool

def Word.is_ne(n, a, b):
  Bool.not(Cmp.is_eq(Word.cmp(n, a, b)))

assert Word.is_lt:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  Bool

def Word.is_lt(n, a, b):
  Cmp.is_lt(Word.cmp(n, a, b))

assert Word.is_le:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  Bool

def Word.is_le(n, a, b):
  Cmp.is_le(Word.cmp(n, a, b))

assert Word.is_gt:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  Bool

def Word.is_gt(n, a, b):
  Cmp.is_gt(Word.cmp(n, a, b))

assert Word.is_ge:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  Bool

def Word.is_ge(n, a, b):
  Cmp.is_ge(Word.cmp(n, a, b))

assert Word.inc:
  forall n: Nat
  forall w: Word(n)
  Word(n)

def Word.inc(n, w):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          WCon{B1(), t}
        case WCon{True{}, t}:
          WCon{B0(), Word.inc(p, t)}

assert Word.adc:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  forall f: Bool
  forall c: Bool
  Word(n)

def Word.adc(n, a, b, f, c):
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

assert Word.add:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  Word(n)

def Word.add(n, a, b):
  Word.adc(n, a, b, B0(), B0())

assert Word.sub:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  Word(n)

def Word.sub(n, a, b):
  Word.adc(n, a, b, B1(), B1())

assert Word.to_nat:
  forall n: Nat
  forall w: Word(n)
  Nat

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

# one shift-add round: (b, (a0 ? b : 0) + 2q + s + carry c), both words
# echoed back at a replicated index, so the caller spends no index copy
assert Word.mul.step:
  forall i: Nat
  forall a0: Bool
  forall s: Bool
  forall c: Bool
  forall b: Word(i)
  forall q: Word(i)
  exists r: Nat
  {i == r : Nat} & Word(r) & Word(r)

def Word.mul.step(i, a0, s, c, b, q):
  match i:
    case 0n:
      match b q:
        case WNil{} WNil{}:
          (0n, {==}, WNil{}, WNil{})
    case 1n+ip:
      match b q:
        case WCon{bb, bt} WCon{qb, qt}:
          ((bb1, x1), (bb2, x2)) = Bool.copy(bb)
          ((a01, y1), (a02, y2)) = Bool.copy(a0)
          (o, k) = Bool.full_add(Bool.and(a01, bb1), s, c)
          (r, er, be, rt) = Word.mul.step(ip, a02, qb, k, bt, qt)
          ce = Equal.cong(Nat, Nat, x => 1n+x, ip, r, er)
          (1n+r, ce, WCon{bb2, be}, WCon{o, rt})

# (b, (a * b) mod 2^i), folding one step per bit of a, echoing b
assert Word.mul.go:
  forall m: Nat
  forall a: Word(m)
  forall i: Nat
  forall b: Word(i)
  exists r: Nat
  {i == r : Nat} & Word(r) & Word(r)

def Word.mul.go(m, a, i, b):
  match m a:
    case 0n WNil{}:
      ((i1, f1), (i2, f2)) = Nat.copy(i)
      ((f1a, u1), (f1b, u2)) = Equal.copy(Nat, i, i1, f1)
      ((f1c, u3), (f1d, u4)) = Equal.copy(Nat, i, i1, f1b)
      z = Word.cast(i2, i1, Equal.trans(Nat, i2, i, i1, Equal.sym(Nat, i, i2, f2), f1c), Word.zero(i2))
      (i1, f1a, Word.cast(i, i1, f1d, b), z)
    case 1n+mp WCon{a0, at}:
      (r1, g1, w1, q) = Word.mul.go(mp, at, i, b)
      (r2, g2, w2, p) = Word.mul.step(r1, a0, B0(), B0(), w1, q)
      (r2, Equal.trans(Nat, i, r1, r2, g1, g2), w2, p)

assert Word.mul:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  Word(n)

def Word.mul(n, a, b):
  ((n1, e1), (n2, e2)) = Nat.copy(n)
  ((e2a, u1), (e2b, u2)) = Equal.copy(Nat, n, n2, e2)
  (r, g, w, p) = Word.mul.go(n1, Word.cast(n, n1, e1, a), n2, Word.cast(n, n2, e2a, b))
  %Equal.sym(Nat, n, r, Equal.trans(Nat, n, n2, r, e2b, g)) : Word(_); p

# U32
# ===

assert U32.zero:
  U32

def U32.zero():
  U32{Word.zero(32n)}

assert U32.one:
  U32

def U32.one():
  U32{Word.inc(32n, Word.zero(32n))}

assert U32.copy:
  forall u: U32
  Copy(U32, u) & Copy(U32, u)

def U32.copy(u):
  match u:
    case U32{w}:
      ((w1, e1), (w2, e2)) = Word.copy(32n, w)
      p1 = Equal.cong(Word(32n), U32, x => U32{x}, w, w1, e1)
      p2 = Equal.cong(Word(32n), U32, x => U32{x}, w, w2, e2)
      ((U32{w1}, p1), (U32{w2}, p2))

assert U32.inc:
  forall a: U32
  U32

def U32.inc(a):
  match a:
    case U32{x}:
      U32{Word.inc(32n, x)}

assert U32.add:
  forall a: U32
  forall b: U32
  U32

def U32.add(a, b):
  match a b:
    case U32{x} U32{y}:
      U32{Word.add(32n, x, y)}

assert U32.sub:
  forall a: U32
  forall b: U32
  U32

def U32.sub(a, b):
  match a b:
    case U32{x} U32{y}:
      U32{Word.sub(32n, x, y)}

assert U32.mul:
  forall a: U32
  forall b: U32
  U32

def U32.mul(a, b):
  match a b:
    case U32{x} U32{y}:
      U32{Word.mul(32n, x, y)}

assert U32.not:
  forall a: U32
  U32

def U32.not(a):
  match a:
    case U32{x}:
      U32{Word.not(32n, x)}

assert U32.and:
  forall a: U32
  forall b: U32
  U32

def U32.and(a, b):
  match a b:
    case U32{x} U32{y}:
      U32{Word.and(32n, x, y)}

assert U32.or:
  forall a: U32
  forall b: U32
  U32

def U32.or(a, b):
  match a b:
    case U32{x} U32{y}:
      U32{Word.or(32n, x, y)}

assert U32.xor:
  forall a: U32
  forall b: U32
  U32

def U32.xor(a, b):
  match a b:
    case U32{x} U32{y}:
      U32{Word.xor(32n, x, y)}

assert U32.shl:
  forall a: U32
  U32

def U32.shl(a):
  match a:
    case U32{x}:
      U32{Word.shl(32n, x)}

assert U32.shr:
  forall a: U32
  U32

def U32.shr(a):
  match a:
    case U32{x}:
      U32{Word.shr(32n, x)}

assert U32.shln:
  forall n: Nat
  forall a: U32
  U32

def U32.shln(n, a):
  match n:
    case 0n:
      a
    case 1n+p:
      U32.shln(p, U32.shl(a))

assert U32.shrn:
  forall n: Nat
  forall a: U32
  U32

def U32.shrn(n, a):
  match n:
    case 0n:
      a
    case 1n+p:
      U32.shrn(p, U32.shr(a))

assert U32.cmp:
  forall a: U32
  forall b: U32
  Cmp

def U32.cmp(a, b):
  match a b:
    case U32{x} U32{y}:
      Word.cmp(32n, x, y)

assert U32.is_eq:
  forall a: U32
  forall b: U32
  Bool

def U32.is_eq(a, b):
  Cmp.is_eq(U32.cmp(a, b))

assert U32.is_ne:
  forall a: U32
  forall b: U32
  Bool

def U32.is_ne(a, b):
  Bool.not(Cmp.is_eq(U32.cmp(a, b)))

assert U32.is_lt:
  forall a: U32
  forall b: U32
  Bool

def U32.is_lt(a, b):
  Cmp.is_lt(U32.cmp(a, b))

assert U32.is_le:
  forall a: U32
  forall b: U32
  Bool

def U32.is_le(a, b):
  Cmp.is_le(U32.cmp(a, b))

assert U32.is_gt:
  forall a: U32
  forall b: U32
  Bool

def U32.is_gt(a, b):
  Cmp.is_gt(U32.cmp(a, b))

assert U32.is_ge:
  forall a: U32
  forall b: U32
  Bool

def U32.is_ge(a, b):
  Cmp.is_ge(U32.cmp(a, b))

assert U32.is_zero:
  forall a: U32
  Bool

def U32.is_zero(a):
  U32.is_eq(a, U32.zero())

assert U32.to_nat:
  forall a: U32
  Nat

def U32.to_nat(a):
  match a:
    case U32{w}:
      Word.to_nat(32n, w)

assert U32.from_nat:
  forall n: Nat
  U32

def U32.from_nat(n):
  match n:
    case 0n:
      U32.zero()
    case 1n+p:
      U32.inc(U32.from_nat(p))

assert U32.div:
  forall a: U32
  forall b: U32
  U32

def U32.div(a, b):
  ((b1, e1), (b2, e2)) = U32.copy(b)
  match U32.is_zero(b1):
    case True{}:
      U32.zero()
    case False{}:
      (q, r) = Nat.divmod(U32.to_nat(a), U32.to_nat(b2))
      U32.from_nat(q)

assert U32.mod:
  forall a: U32
  forall b: U32
  U32

def U32.mod(a, b):
  ((b1, e1), (b2, e2)) = U32.copy(b)
  match U32.is_zero(b1):
    case True{}:
      U32.zero()
    case False{}:
      (q, r) = Nat.divmod(U32.to_nat(a), U32.to_nat(b2))
      U32.from_nat(r)

# String
# ======

assert String.append:
  forall a: String
  forall b: String
  String

def String.append(a, b):
  match a:
    case SNil{}:
      b
    case SCon{h, t}:
      SCon{h, String.append(t, b)}

# Array
# =====

assert Array.swap:
  forall -T: Type
  forall a: Array<T>
  forall i: U32
  forall v: T
  Array<T> & T

def Array.swap(T, a, i, v):
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
