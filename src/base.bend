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

type Par<A: Type, B: Type>:
  Both{fst: A, snd: B}

type Sigma<-A: Type, -B: @-x: A -> Type>:
  Tuple{fst: A, snd: B(fst)}

def Pair(-A: Type, -B: Type) -> Type:
  Sigma<A, _ => B>

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

type Fiber<-A: Type>:
  Fiber{slot: U32, gen: U32}

type File:
  File{slot: U32, gen: U32}

type Socket:
  Socket{slot: U32, gen: U32}

type Listener:
  Listener{slot: U32, gen: U32}

type Sender<-A: Type>:
  Sender{slot: U32, gen: U32}

type Receiver<-A: Type>:
  Receiver{slot: U32, gen: U32}

type IO.OP<-R: Type>:
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

assert Nat.half:
  forall m: Nat
  Nat

def Nat.half(m):
  match m:
    case 0n:
      0n
    case 1n:
      0n
    case 2n+r:
      1n+Nat.half(r)

assert Nat.even:
  forall m: Nat
  Bool

def Nat.even(m):
  match m:
    case 0n:
      True{}
    case 1n:
      False{}
    case 2n+r:
      Nat.even(r)

# half and even against double: each arm rides one cong (or the IH
# alone) over the two-peel ladder
assert Nat.half_double:
  forall m: Nat
  {Nat.half(Nat.double(m)) == m : Nat}

def Nat.half_double(m):
  match m:
    case 0n:
      {==}
    case 1n+q:
      Equal.cong(Nat, Nat, y => 1n+y, Nat.half(Nat.double(q)), q, Nat.half_double(q))

assert Nat.half_double_succ:
  forall m: Nat
  {Nat.half(1n+Nat.double(m)) == m : Nat}

def Nat.half_double_succ(m):
  match m:
    case 0n:
      {==}
    case 1n+q:
      Equal.cong(Nat, Nat, y => 1n+y, Nat.half(1n+Nat.double(q)), q, Nat.half_double_succ(q))

assert Nat.even_double:
  forall m: Nat
  {Nat.even(Nat.double(m)) == True{} : Bool}

def Nat.even_double(m):
  match m:
    case 0n:
      {==}
    case 1n+q:
      Nat.even_double(q)

assert Nat.even_double_succ:
  forall m: Nat
  {Nat.even(1n+Nat.double(m)) == False{} : Bool}

def Nat.even_double_succ(m):
  match m:
    case 0n:
      {==}
    case 1n+q:
      Nat.even_double_succ(q)

# the order FAMILY: LE(a, b) computes to Unit when a <= b, Empty otherwise
assert Nat.LE:
  forall a: Nat
  forall b: Nat
  Type

def Nat.LE(a, b):
  match a b:
    case 0n y:
      Unit
    case 1n+x 0n:
      Empty
    case 1n+x 1n+y:
      Nat.LE(x, y)

assert Nat.le_refl:
  forall a: Nat
  Nat.LE(a, a)

def Nat.le_refl(a):
  match a:
    case 0n:
      Unit{}
    case 1n+x:
      Nat.le_refl(x)

assert Nat.le_zero:
  forall -b: Nat
  Nat.LE(0n, b)

def Nat.le_zero(b):
  Unit{}

assert Nat.le_succ:
  forall a: Nat
  forall b: Nat
  forall e: Nat.LE(a, b)
  Nat.LE(a, 1n+b)

def Nat.le_succ(a, b, e):
  match a:
    case 0n:
      Unit{}
    case 1n+x:
      match b:
        case 0n:
          Empty.absurd(Nat.LE(x, 0n), e)
        case 1n+y:
          Nat.le_succ(x, y, e)

assert Nat.le_trans:
  forall a: Nat
  forall b: Nat
  forall c: Nat
  forall ab: Nat.LE(a, b)
  forall bc: Nat.LE(b, c)
  Nat.LE(a, c)

def Nat.le_trans(a, b, c, ab, bc):
  match a:
    case 0n:
      Unit{}
    case 1n+x:
      match b:
        case 0n:
          Empty.absurd(Nat.LE(1n+x, c), ab)
        case 1n+y:
          match c:
            case 0n:
              Empty.absurd(Nat.LE(1n+x, 0n), bc)
            case 1n+z:
              Nat.le_trans(x, y, z, ab, bc)

assert Nat.le_antisym:
  forall a: Nat
  forall b: Nat
  forall ab: Nat.LE(a, b)
  forall ba: Nat.LE(b, a)
  {a == b : Nat}

def Nat.le_antisym(a, b, ab, ba):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      Empty.absurd({0n == 1n+y : Nat}, ba)
    case 1n+x 0n:
      Empty.absurd({1n+x == 0n : Nat}, ab)
    case 1n+x 1n+y:
      Equal.cong(Nat, Nat, k => 1n+k, x, y, Nat.le_antisym(x, y, ab, ba))

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

assert List.is_empty:
  forall -A: Type
  forall xs: List<A>
  Bool

def List.is_empty(A, xs):
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

assert List.head:
  forall -A: Type
  forall xs: List<A>
  Maybe<A>

def List.head(A, xs):
  match xs:
    case Nil{}:
      None{}
    case Con{h, t}:
      Some{h}

assert List.tail:
  forall -A: Type
  forall xs: List<A>
  List<A>

def List.tail(A, xs):
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

assert List.get:
  forall -A: Type
  forall n: Nat
  forall xs: List<A>
  Maybe<A>

def List.get(A, n, xs):
  match n xs:
    case 0n Nil{}:
      None{}
    case 0n Con{h, t}:
      Some{h}
    case 1n+p Nil{}:
      None{}
    case 1n+p Con{h, t}:
      List.get(A, p, t)

assert List.set:
  forall -A: Type
  forall n: Nat
  forall x: A
  forall xs: List<A>
  List<A>

def List.set(A, n, x, xs):
  match n xs:
    case 0n Nil{}:
      Nil{}
    case 0n Con{h, t}:
      Con{x, t}
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{h, t}:
      Con{h, List.set(A, p, x, t)}

assert List.concat:
  forall -A: Type
  forall xss: List<List<A>>
  List<A>

def List.concat(A, xss):
  match xss:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      List.append(A, h, List.concat(A, t))

assert List.zip:
  forall -A: Type
  forall -B: Type
  forall xs: List<A>
  forall ys: List<B>
  List<(A & B)>

def List.zip(A, B, xs, ys):
  match xs ys:
    case Nil{} Nil{}:
      Nil{}
    case Nil{} Con{h, t}:
      Nil{}
    case Con{h, t} Nil{}:
      Nil{}
    case Con{a, at} Con{b, bt}:
      Con{(a, b), List.zip(A, B, at, bt)}

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

# Word.shl.put that also hands back the bit that fell off the top --
# the carry of a doubling
assert Word.shl.out:
  forall n: Nat
  forall c: Bool
  forall w: Word(n)
  Bool & Word(n)

def Word.shl.out(n, c, w):
  match n:
    case 0n:
      (c, WNil{})
    case 1n+p:
      match w:
        case WCon{b, t}:
          (hi, t2) = Word.shl.out(p, b, t)
          (hi, WCon{c, t2})

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

# addition is commutative at any carry: the full adder is symmetric in
# its two operand bits, so each column rides one cong over the IH
assert Word.add_comm.go:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  forall c: Bool
  {Word.adc(n, a, b, B0(), c) == Word.adc(n, b, a, B0(), c) : Word(n)}

def Word.add_comm.go(n, a, b, c):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, at} WCon{False{}, bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{B0(), w}, Word.adc(p, at, bt, B0(), B0()), Word.adc(p, bt, at, B0(), B0()), Word.add_comm.go(p, at, bt, B0()))
        case WCon{False{}, at} WCon{False{}, bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{B1(), w}, Word.adc(p, at, bt, B0(), B0()), Word.adc(p, bt, at, B0(), B0()), Word.add_comm.go(p, at, bt, B0()))
        case WCon{False{}, at} WCon{True{}, bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{B1(), w}, Word.adc(p, at, bt, B0(), B0()), Word.adc(p, bt, at, B0(), B0()), Word.add_comm.go(p, at, bt, B0()))
        case WCon{False{}, at} WCon{True{}, bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{B0(), w}, Word.adc(p, at, bt, B0(), B1()), Word.adc(p, bt, at, B0(), B1()), Word.add_comm.go(p, at, bt, B1()))
        case WCon{True{}, at} WCon{False{}, bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{B1(), w}, Word.adc(p, at, bt, B0(), B0()), Word.adc(p, bt, at, B0(), B0()), Word.add_comm.go(p, at, bt, B0()))
        case WCon{True{}, at} WCon{False{}, bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{B0(), w}, Word.adc(p, at, bt, B0(), B1()), Word.adc(p, bt, at, B0(), B1()), Word.add_comm.go(p, at, bt, B1()))
        case WCon{True{}, at} WCon{True{}, bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{B0(), w}, Word.adc(p, at, bt, B0(), B1()), Word.adc(p, bt, at, B0(), B1()), Word.add_comm.go(p, at, bt, B1()))
        case WCon{True{}, at} WCon{True{}, bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{B1(), w}, Word.adc(p, at, bt, B0(), B1()), Word.adc(p, bt, at, B0(), B1()), Word.add_comm.go(p, at, bt, B1()))

assert Word.add_comm:
  forall n: Nat
  forall a: Word(n)
  forall b: Word(n)
  {Word.add(n, a, b) == Word.add(n, b, a) : Word(n)}

def Word.add_comm(n, a, b):
  Word.add_comm.go(n, a, b, B0())

# zero is right-neutral: the carry stays low, so each column is one
# cong over the IH
assert Word.add_zero:
  forall n: Nat
  forall w: Word(n)
  {Word.add(n, w, Word.zero(n)) == w : Word(n)}

def Word.add_zero(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          Equal.cong(Word(p), Word(1n+p), y => WCon{B0(), y}, Word.add(p, t, Word.zero(p)), t, Word.add_zero(p, t))
        case WCon{True{}, t}:
          Equal.cong(Word(p), Word(1n+p), y => WCon{B1(), y}, Word.add(p, t, Word.zero(p)), t, Word.add_zero(p, t))

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

# a zero pad at the top does not move the value
assert Word.shr.pad_to_nat:
  forall n: Nat
  forall w: Word(n)
  {Word.to_nat(1n+n, Word.shr.pad(n, w)) == Word.to_nat(n, w) : Nat}

def Word.shr.pad_to_nat(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+q:
      match w:
        case WCon{False{}, t}:
          Equal.cong(Nat, Nat, y => Nat.double(y), Word.to_nat(1n+q, Word.shr.pad(q, t)), Word.to_nat(q, t), Word.shr.pad_to_nat(q, t))
        case WCon{True{}, t}:
          Equal.cong(Nat, Nat, y => 1n+Nat.double(y), Word.to_nat(1n+q, Word.shr.pad(q, t)), Word.to_nat(q, t), Word.shr.pad_to_nat(q, t))

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

assert U32.add_comm:
  forall a: U32
  forall b: U32
  {U32.add(a, b) == U32.add(b, a) : U32}

def U32.add_comm(a, b):
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.add(32n, x, y), Word.add(32n, y, x), Word.add_comm(32n, x, y))

assert U32.add_zero:
  forall a: U32
  {U32.add(a, U32.zero()) == a : U32}

def U32.add_zero(a):
  match a:
    case U32{x}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.add(32n, x, Word.zero(32n)), x, Word.add_zero(32n, x))

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

# iterated shifts compose by count addition (no count mask exists:
# shifting past the width shifts out)
assert U32.shln_add:
  forall k: Nat
  forall m: Nat
  forall a: U32
  {U32.shln(k, U32.shln(m, a)) == U32.shln(Nat.add(m, k), a) : U32}

def U32.shln_add(k, m, a):
  match m:
    case 0n:
      {==}
    case 1n+q:
      U32.shln_add(k, q, U32.shl(a))

assert U32.shrn_add:
  forall k: Nat
  forall m: Nat
  forall a: U32
  {U32.shrn(k, U32.shrn(m, a)) == U32.shrn(Nat.add(m, k), a) : U32}

def U32.shrn_add(k, m, a):
  match m:
    case 0n:
      {==}
    case 1n+q:
      U32.shrn_add(k, q, U32.shr(a))

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

# a left shift lands a zero low bit, so its value is even -- for EVERY
# word, wrap included
assert U32.shl_even.go:
  forall w: Word(32n)
  {Nat.even(Word.to_nat(32n, Word.shl(32n, w))) == True{} : Bool}

def U32.shl_even.go(w):
  match w:
    case WCon{b, t}:
      Nat.even_double(Word.to_nat(31n, Word.shl.put(31n, b, t)))

assert U32.shl_even:
  forall a: U32
  {Nat.even(U32.to_nat(U32.shl(a))) == True{} : Bool}

def U32.shl_even(a):
  match a:
    case U32{w}:
      U32.shl_even.go(w)

# binary long division on the word itself, one round per dividend bit,
# walking from the top bit down: r <- 2r + bit, minus b when it fits,
# and "fits" is the quotient bit. A doubling that overflows the width
# forces the bit -- the true 2r + bit is then past 2^32 > b -- and the
# wrapping U32.sub still lands the true remainder (it sits under b, so
# under 2^32). Needs b > 0: the callers guard.
assert U32.divmod.go:
  forall m: Nat
  forall a: Word(m)
  forall b: U32
  Word(m) & U32

def U32.divmod.go(m, a, b):
  match m a:
    case 0n WNil{}:
      (WNil{}, U32.zero())
    case 1n+p WCon{a0, hi}:
      ((b1, e1), (b2, e2)) = U32.copy(b)
      (q, r) = U32.divmod.go(p, hi, b1)
      U32{rw} = r
      ((b3, e3), (b4, e4)) = U32.copy(b2)
      (t, s) = Word.shl.out(32n, a0, rw)
      ((s1, e5), (s2, e6)) = Word.copy(32n, s)
      match Bool.or(t, U32.is_ge(U32{s1}, b3)):
        case True{}:
          (WCon{B1(), q}, U32.sub(U32{s2}, b4))
        case False{}:
          (WCon{B0(), q}, U32{s2})

# at b = 0 the pair keeps Nat.divmod's own convention -- div answers 0,
# mod the dividend -- so a = b * div(a,b) + mod(a,b) holds at every b.
assert U32.div:
  forall a: U32
  forall b: U32
  U32

def U32.div(a, b):
  U32{aw} = a
  ((b1, e1), (b2, e2)) = U32.copy(b)
  match U32.is_zero(b1):
    case True{}:
      U32.zero()
    case False{}:
      (q, r) = U32.divmod.go(32n, aw, b2)
      U32{q}

assert U32.mod:
  forall a: U32
  forall b: U32
  U32

def U32.mod(a, b):
  U32{aw} = a
  ((b1, e1), (b2, e2)) = U32.copy(b)
  match U32.is_zero(b1):
    case True{}:
      U32{aw}
    case False{}:
      (q, r) = U32.divmod.go(32n, aw, b2)
      r

# F32
# ===
#
# IEEE-754 binary32 as an axiom family: unfilled asserts, stuck in the
# checker, native in every backend.

assert F32:
  Type

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

# a float literal m.f desugars to F32.make(digits, scale): the one home
# of the division spelling
assert F32.make:
  forall m: U32
  forall s: U32
  F32

def F32.make(m, s):
  F32.div(U32.to_f32(m), U32.to_f32(s))

# Char
# ====

assert Char.copy:
  forall c: Char
  Char & Char

def Char.copy(c):
  match c:
    case Chr{x}:
      ((x1, e1), (x2, e2)) = U32.copy(x)
      (Chr{x1}, Chr{x2})

# leftovers first, the decision last, so the caller can match it
assert Char.cmp:
  forall a: Char
  forall b: Char
  (Char & Char) & Cmp

def Char.cmp(a, b):
  match a b:
    case Chr{x} Chr{y}:
      ((x1, e1), (x2, e2)) = U32.copy(x)
      ((y1, f1), (y2, f2)) = U32.copy(y)
      ((Chr{x2}, Chr{y2}), U32.cmp(x1, y1))

assert Char.eq:
  forall a: Char
  forall b: Char
  (Char & Char) & Bool

def Char.eq(a, b):
  ((a2, b2), c) = Char.cmp(a, b)
  ((a2, b2), Cmp.is_eq(c))

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

assert String.copy:
  forall s: String
  String & String

def String.copy(s):
  match s:
    case SNil{}:
      (SNil{}, SNil{})
    case SCon{h, t}:
      (h1, h2) = Char.copy(h)
      (t1, t2) = String.copy(t)
      (SCon{h1, t1}, SCon{h2, t2})

# code-point order; a shorter prefix sorts first
assert String.cmp:
  forall a: String
  forall b: String
  (String & String) & Cmp

def String.cmp(a, b):
  match a b:
    case SNil{} SNil{}:
      ((SNil{}, SNil{}), EQ{})
    case SNil{} SCon{h, t}:
      ((SNil{}, SCon{h, t}), LT{})
    case SCon{h, t} SNil{}:
      ((SCon{h, t}, SNil{}), GT{})
    case SCon{h1, t1} SCon{h2, t2}:
      ((h1b, h2b), c) = Char.cmp(h1, h2)
      match c:
        case LT{}:
          ((SCon{h1b, t1}, SCon{h2b, t2}), LT{})
        case EQ{}:
          ((t1b, t2b), r) = String.cmp(t1, t2)
          ((SCon{h1b, t1b}, SCon{h2b, t2b}), r)
        case GT{}:
          ((SCon{h1b, t1}, SCon{h2b, t2}), GT{})

assert String.eq:
  forall a: String
  forall b: String
  Bool

def String.eq(a, b):
  ((a2, b2), c) = String.cmp(a, b)
  Cmp.is_eq(c)

assert String.length:
  forall s: String
  Nat

def String.length(s):
  match s:
    case SNil{}:
      0n
    case SCon{h, t}:
      1n+String.length(t)

assert String.split.push:
  forall c: Char
  forall ps: List<String>
  List<String>

def String.split.push(c, ps):
  match ps:
    case Nil{}:
      Con{SCon{c, SNil{}}, Nil{}}
    case Con{h, t}:
      Con{SCon{c, h}, t}

# every separator opens a group, so "a,b" has two and "," has two
assert String.split:
  forall s: String
  forall sep: Char
  List<String>

def String.split(s, sep):
  match s:
    case SNil{}:
      Con{SNil{}, Nil{}}
    case SCon{h, t}:
      ((h2, sep2), e) = Char.eq(h, sep)
      match e:
        case True{}:
          Con{SNil{}, String.split(t, sep2)}
        case False{}:
          String.split.push(h2, String.split(t, sep2))

assert String.join.go:
  forall xs: List<String>
  forall h: String
  forall sep: String
  String

def String.join.go(xs, h, sep):
  match xs:
    case Nil{}:
      h
    case Con{h2, t2}:
      (s1, s2) = String.copy(sep)
      String.append(h, String.append(s1, String.join.go(t2, h2, s2)))

assert String.join:
  forall xs: List<String>
  forall sep: String
  String

def String.join(xs, sep):
  match xs:
    case Nil{}:
      SNil{}
    case Con{h, t}:
      String.join.go(t, h, sep)

# Text
# ====
#
# Decimal number <-> text. show is total; read takes one or more
# decimal digits and answers None on anything else (U32.read folds
# left, wrapping mod 2^32).

assert U32.read.dig:
  forall c: Char
  Maybe<U32>

def U32.read.dig(c):
  match c:
    case Chr{x}:
      ((x1, e1), (x2, e2)) = U32.copy(x)
      ((x3, e3), (x4, e4)) = U32.copy(x2)
      match Bool.and(U32.is_le(48, x1), U32.is_le(x3, 57)):
        case True{}:
          Some{U32.sub(x4, 48)}
        case False{}:
          None{}

# one digit off the low end: the digit's char, the quotient last
assert Nat.show.step:
  forall n: Nat
  Char & Nat

def Nat.show.step(n):
  (q, r) = Nat.divmod(n, 10n)
  (Chr{U32.from_nat(Nat.add(48n, r))}, q)

assert Nat.show.go:
  forall f: Nat
  forall n: Nat
  forall acc: String
  String

def Nat.show.go(f, n, acc):
  match f:
    case 0n:
      acc
    case 1n+g:
      (d, q) = Nat.show.step(n)
      match q:
        case 0n:
          SCon{d, acc}
        case 1n+p:
          Nat.show.go(g, 1n+p, SCon{d, acc})

# the number is its own digit-count fuel
assert Nat.show:
  forall n: Nat
  String

def Nat.show(n):
  ((n1, e1), (n2, e2)) = Nat.copy(n)
  Nat.show.go(1n+n1, n2, SNil{})

assert Nat.read.go:
  forall s: String
  forall acc: Nat
  Maybe<Nat>

def Nat.read.go(s, acc):
  match s:
    case SNil{}:
      Some{acc}
    case SCon{h, t}:
      match U32.read.dig(h):
        case None{}:
          None{}
        case Some{d}:
          Nat.read.go(t, Nat.add(Nat.mul(acc, 10n), U32.to_nat(d)))

assert Nat.read:
  forall s: String
  Maybe<Nat>

def Nat.read(s):
  match s:
    case SNil{}:
      None{}
    case SCon{h, t}:
      Nat.read.go(SCon{h, t}, 0n)

assert U32.show.go:
  forall f: Nat
  forall n: U32
  forall acc: String
  String

def U32.show.go(f, n, acc):
  match f:
    case 0n:
      acc
    case 1n+g:
      ((n1, e1), (n2, e2)) = U32.copy(n)
      ((n3, e3), (n4, e4)) = U32.copy(n2)
      match U32.is_zero(n1):
        case True{}:
          acc
        case False{}:
          U32.show.go(g, U32.div(n3, 10), SCon{Chr{U32.add(48, U32.mod(n4, 10))}, acc})

assert U32.show:
  forall a: U32
  String

def U32.show(a):
  ((a1, e1), (a2, e2)) = U32.copy(a)
  match U32.is_zero(a1):
    case True{}:
      SCon{Chr{48}, SNil{}}
    case False{}:
      U32.show.go(10n, a2, SNil{})

assert U32.read.go:
  forall s: String
  forall acc: U32
  Maybe<U32>

def U32.read.go(s, acc):
  match s:
    case SNil{}:
      Some{acc}
    case SCon{h, t}:
      match U32.read.dig(h):
        case None{}:
          None{}
        case Some{d}:
          U32.read.go(t, U32.add(U32.mul(acc, 10), d))

assert U32.read:
  forall s: String
  Maybe<U32>

def U32.read(s):
  match s:
    case SNil{}:
      None{}
    case SCon{h, t}:
      U32.read.go(SCon{h, t}, 0)

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

assert Array.copy:
  forall a: Array<U32>
  Array<U32> & Array<U32>

def Array.copy(a):
  match a:
    case ALeaf{x}:
      ((x1, e1), (x2, e2)) = U32.copy(x)
      (ALeaf{x1}, ALeaf{x2})
    case ANode{xs, ys}:
      (xa, xb) = Array.copy(xs)
      (ya, yb) = Array.copy(ys)
      (ANode{xa, ya}, ANode{xb, yb})

assert Array.new:
  forall d: Nat
  forall v: U32
  Array<U32>

def Array.new(d, v):
  match d:
    case 0n:
      ALeaf{v}
    case 1n+p:
      (l, r) = Array.copy(Array.new(p, v))
      ANode{l, r}

assert Array.set:
  forall a: Array<U32>
  forall i: U32
  forall v: U32
  Array<U32>

def Array.set(a, i, v):
  (na, old) = Array.swap(U32, a, i, v)
  na

assert Array.get:
  forall a: Array<U32>
  forall i: U32
  Array<U32> & U32

def Array.get(a, i):
  match a:
    case ALeaf{x}:
      ((x1, e1), (x2, e2)) = U32.copy(x)
      (ALeaf{x1}, x2)
    case ANode{xs, ys}:
      ((i1, e1), (i2, e2)) = U32.copy(i)
      match U32.is_zero(U32.and(i1, U32.one())):
        case True{}:
          (nxs, x) = Array.get(xs, U32.shr(i2))
          (ANode{nxs, ys}, x)
        case False{}:
          (nys, x) = Array.get(ys, U32.shr(i2))
          (ANode{xs, nys}, x)

# Map
# ===
# The string-keyed immutable map: ONE representation, a PATRICIA
# (crit-bit) tree over the key's own char codes -- no hashing, so no
# collisions, the shape is a function of the key set alone, and
# to_list walks it in code-point order. A crit-bit position is
# pos = char_index * 33 + offset (a Nat): offset 0 is the "a char
# exists here" presence bit and offset 1 + b is bit b of that char's
# code, most-significant-first, so an exhausted key reads 0 everywhere
# and positions order lexicographically. An MNode's pos strictly
# increases downward: lookup follows the key's bit at pos (0 -> lo,
# 1 -> hi) to one leaf, then a single key comparison decides; set
# seeks that leaf and either replaces it in place (put) or splices an
# MNode at the first differing position (ins). Every walk hands its
# leftovers back, the decision last. get cannot copy an open V, so it
# takes the copier for V as its first runtime argument.

type Map<-V: Type>:
  MTip{}
  MLeaf{key: String, val: V}
  MNode{pos: Nat, lo: Map<V>, hi: Map<V>}

# bit k of a code, least-significant-first, through the word natives
assert Map.bit.u:
  forall x: U32
  forall k: Nat
  Bool

def Map.bit.u(x, k):
  U32.is_ne(U32.and(U32.shrn(k, x), 1), 0)

# a char's crit-bit at an in-char offset: 0 is presence, 1 + b reads
# bit b of the code, most-significant-first
assert Map.bit.chr:
  forall c: Char
  forall off: Nat
  Char & Bool

def Map.bit.chr(c, off):
  match c:
    case Chr{x}:
      match off:
        case 0n:
          (Chr{x}, True{})
        case 1n+b:
          ((x1, e1), (x2, e2)) = U32.copy(x)
          (Chr{x1}, Map.bit.u(x2, Nat.sub(31n, b)))

assert Map.bit.go:
  forall key: String
  forall ci: Nat
  forall off: Nat
  String & Bool

def Map.bit.go(key, ci, off):
  match key:
    case SNil{}:
      (SNil{}, False{})
    case SCon{c, t}:
      match ci:
        case 0n:
          (c2, b) = Map.bit.chr(c, off)
          (SCon{c2, t}, b)
        case 1n+j:
          (t2, b) = Map.bit.go(t, j, off)
          (SCon{c, t2}, b)

# the key's crit-bit at a position (an exhausted key reads 0)
assert Map.bit:
  forall key: String
  forall pos: Nat
  String & Bool

def Map.bit(key, pos):
  match Nat.divmod(pos, 33n):
    case (ci, off):
      Map.bit.go(key, ci, off)

# the bit count of a code: its highest set bit's index plus one,
# by fueled halving through the word natives
assert Map.msb.u:
  forall n: Nat
  forall x: U32
  Nat

def Map.msb.u(n, x):
  match n:
    case 0n:
      0n
    case 1n+p:
      ((x1, e1), (x2, e2)) = U32.copy(x)
      match U32.is_zero(x1):
        case True{}:
          0n
        case False{}:
          Nat.add(1n, Map.msb.u(p, U32.shr(x2)))

# the in-char offset where two distinct codes first differ, from
# their xor: 33 minus its bit count
assert Map.diff.chr:
  forall x: U32
  Nat

def Map.diff.chr(x):
  Nat.sub(33n, Map.msb.u(32n, x))

# leftmost: the offset if the chars differ; rightmost: whether they
# are equal (the offset is garbage then, and dropped)
assert Map.diff.step:
  forall x: Char
  forall y: Char
  Nat & Bool

def Map.diff.step(x, y):
  match x y:
    case Chr{cx} Chr{cy}:
      ((cx1, e1), (cx2, e2)) = U32.copy(cx)
      ((cy1, f1), (cy2, f2)) = U32.copy(cy)
      (Map.diff.chr(U32.xor(cx2, cy2)), U32.is_eq(cx1, cy1))

# the first crit-bit position where two distinct keys differ (each
# agreeing char adds its 33 positions on the way out)
assert Map.diff:
  forall a: String
  forall b: String
  Nat

def Map.diff(a, b):
  match a b:
    case SNil{} SNil{}:
      0n
    case SNil{} SCon{h, t}:
      0n
    case SCon{h, t} SNil{}:
      0n
    case SCon{x, xt} SCon{y, yt}:
      (r, c) = Map.diff.step(x, y)
      match c:
        case True{}:
          Nat.add(33n, Map.diff(xt, yt))
        case False{}:
          r

assert Map.new:
  forall -V: Type
  Map<V>

def Map.new(V):
  MTip{}

# replace at the leaf the key's bits lead to (the key is known held)
assert Map.put:
  forall -V: Type
  forall m: Map<V>
  forall key: String
  forall x: V
  Map<V>

def Map.put(V, m, key, x):
  match m:
    case MTip{}:
      MLeaf{key, x}
    case MLeaf{k, v}:
      MLeaf{k, x}
    case MNode{pos, lo, hi}:
      ((p1, e1), (p2, e2)) = Nat.copy(pos)
      (key2, b) = Map.bit(key, p1)
      match b:
        case False{}:
          MNode{p2, Map.put(V, lo, key2, x), hi}
        case True{}:
          MNode{p2, lo, Map.put(V, hi, key2, x)}

assert Map.ins.splice:
  forall -V: Type
  forall p: Nat
  forall key: String
  forall x: V
  forall rest: Map<V>
  Map<V>

def Map.ins.splice(V, p, key, x, rest):
  ((pa, e1), (pb, e2)) = Nat.copy(p)
  (key2, b) = Map.bit(key, pa)
  match b:
    case False{}:
      MNode{pb, MLeaf{key2, x}, rest}
    case True{}:
      MNode{pb, rest, MLeaf{key2, x}}

# splice a new leaf at position p, above the first deeper position
assert Map.ins:
  forall -V: Type
  forall m: Map<V>
  forall key: String
  forall x: V
  forall p: Nat
  Map<V>

def Map.ins(V, m, key, x, p):
  match m:
    case MTip{}:
      MLeaf{key, x}
    case MLeaf{k, v}:
      Map.ins.splice(V, p, key, x, MLeaf{k, v})
    case MNode{pos, lo, hi}:
      ((pos1, e1), (pos2, e2)) = Nat.copy(pos)
      ((pa, f1), (pb, f2)) = Nat.copy(p)
      match Nat.is_lt(pos1, pa):
        case False{}:
          Map.ins.splice(V, pb, key, x, MNode{pos2, lo, hi})
        case True{}:
          ((qa, g1), (qb, g2)) = Nat.copy(pos2)
          (key2, b) = Map.bit(key, qa)
          match b:
            case False{}:
              MNode{qb, Map.ins(V, lo, key2, x, pb), hi}
            case True{}:
              MNode{qb, lo, Map.ins(V, hi, key2, x, pb)}

# walk the key's bits to its leaf; rightmost: that leaf's key, if any
assert Map.seek:
  forall -V: Type
  forall m: Map<V>
  forall key: String
  (Map<V> & String) & Maybe<String>

def Map.seek(V, m, key):
  match m:
    case MTip{}:
      ((MTip{}, key), None{})
    case MLeaf{k, v}:
      (k1, k2) = String.copy(k)
      ((MLeaf{k1, v}, key), Some{k2})
    case MNode{pos, lo, hi}:
      ((p1, e1), (p2, e2)) = Nat.copy(pos)
      (key2, b) = Map.bit(key, p1)
      match b:
        case False{}:
          ((lo2, key3), r) = Map.seek(V, lo, key2)
          ((MNode{p2, lo2, hi}, key3), r)
        case True{}:
          ((hi2, key3), r) = Map.seek(V, hi, key2)
          ((MNode{p2, lo, hi2}, key3), r)

assert Map.set.fin:
  forall -V: Type
  forall m: Map<V>
  forall key: String
  forall x: V
  forall keyb: String
  forall k: String
  Map<V>

def Map.set.fin(V, m, key, x, keyb, k):
  ((keyb2, k2), c) = String.cmp(keyb, k)
  match c:
    case LT{}:
      Map.ins(V, m, key, x, Map.diff(keyb2, k2))
    case EQ{}:
      Map.put(V, m, key, x)
    case GT{}:
      Map.ins(V, m, key, x, Map.diff(keyb2, k2))

# insert or replace: seek the key's leaf, then replace in place or
# splice at the first differing position
assert Map.set:
  forall -V: Type
  forall m: Map<V>
  forall key: String
  forall x: V
  Map<V>

def Map.set(V, m, key, x):
  ((m2, key2), found) = Map.seek(V, m, key)
  match found:
    case None{}:
      MLeaf{key2, x}
    case Some{k}:
      (ka, kb) = String.copy(key2)
      Map.set.fin(V, m2, ka, x, kb, k)

assert Map.set.kv:
  forall -V: Type
  forall m: Map<V>
  forall kv: String & V
  Map<V>

def Map.set.kv(V, m, kv):
  (k, v) = kv
  Map.set(V, m, k, v)

assert Map.has:
  forall -V: Type
  forall m: Map<V>
  forall key: String
  Map<V> & Bool

def Map.has(V, m, key):
  match m:
    case MTip{}:
      (MTip{}, False{})
    case MLeaf{k, v}:
      ((key2, k2), c) = String.cmp(key, k)
      (MLeaf{k2, v}, Cmp.is_eq(c))
    case MNode{pos, lo, hi}:
      ((p1, e1), (p2, e2)) = Nat.copy(pos)
      (key2, b) = Map.bit(key, p1)
      match b:
        case False{}:
          (lo2, r) = Map.has(V, lo, key2)
          (MNode{p2, lo2, hi}, r)
        case True{}:
          (hi2, r) = Map.has(V, hi, key2)
          (MNode{p2, lo, hi2}, r)

# the value under the key, or the default; cp copies a V, since an
# open V cannot be copied here
assert Map.get:
  forall -V: Type
  forall cp: V -> (V & V)
  forall d: V
  forall m: Map<V>
  forall key: String
  Map<V> & V

def Map.get(V, cp, d, m, key):
  match m:
    case MTip{}:
      (MTip{}, d)
    case MLeaf{k, v}:
      ((key2, k2), c) = String.cmp(key, k)
      match c:
        case LT{}:
          (MLeaf{k2, v}, d)
        case EQ{}:
          (v1, v2) = cp(v)
          (MLeaf{k2, v1}, v2)
        case GT{}:
          (MLeaf{k2, v}, d)
    case MNode{pos, lo, hi}:
      ((p1, e1), (p2, e2)) = Nat.copy(pos)
      (key2, b) = Map.bit(key, p1)
      match b:
        case False{}:
          (lo2, r) = Map.get(V, cp, d, lo, key2)
          (MNode{p2, lo2, hi}, r)
        case True{}:
          (hi2, r) = Map.get(V, cp, d, hi, key2)
          (MNode{p2, lo, hi2}, r)

# a vacated MNode collapses to its other child, so MTip never sits
# under an MNode
assert Map.pop.lo:
  forall -V: Type
  forall pos: Nat
  forall lo: Map<V>
  forall hi: Map<V>
  forall r: Maybe<V>
  Map<V> & Maybe<V>

def Map.pop.lo(V, pos, lo, hi, r):
  match lo:
    case MTip{}:
      (hi, r)
    case MLeaf{k, v}:
      (MNode{pos, MLeaf{k, v}, hi}, r)
    case MNode{p, a, b}:
      (MNode{pos, MNode{p, a, b}, hi}, r)

assert Map.pop.hi:
  forall -V: Type
  forall pos: Nat
  forall lo: Map<V>
  forall hi: Map<V>
  forall r: Maybe<V>
  Map<V> & Maybe<V>

def Map.pop.hi(V, pos, lo, hi, r):
  match hi:
    case MTip{}:
      (lo, r)
    case MLeaf{k, v}:
      (MNode{pos, lo, MLeaf{k, v}}, r)
    case MNode{p, a, b}:
      (MNode{pos, lo, MNode{p, a, b}}, r)

# removes and returns the value: it moves out, no copy of V needed
assert Map.pop:
  forall -V: Type
  forall m: Map<V>
  forall key: String
  Map<V> & Maybe<V>

def Map.pop(V, m, key):
  match m:
    case MTip{}:
      (MTip{}, None{})
    case MLeaf{k, v}:
      ((key2, k2), c) = String.cmp(key, k)
      match c:
        case LT{}:
          (MLeaf{k2, v}, None{})
        case EQ{}:
          (MTip{}, Some{v})
        case GT{}:
          (MLeaf{k2, v}, None{})
    case MNode{pos, lo, hi}:
      ((p1, e1), (p2, e2)) = Nat.copy(pos)
      (key2, b) = Map.bit(key, p1)
      match b:
        case False{}:
          (lo2, r) = Map.pop(V, lo, key2)
          Map.pop.lo(V, p2, lo2, hi, r)
        case True{}:
          (hi2, r) = Map.pop(V, hi, key2)
          Map.pop.hi(V, p2, lo, hi2, r)

assert Map.del:
  forall -V: Type
  forall m: Map<V>
  forall key: String
  Map<V>

def Map.del(V, m, key):
  match Map.pop(V, m, key):
    case (m2, r):
      m2

# the entry count (consumes, like List.length)
assert Map.size:
  forall -V: Type
  forall m: Map<V>
  Nat

def Map.size(V, m):
  match m:
    case MTip{}:
      0n
    case MLeaf{k, v}:
      1n
    case MNode{pos, lo, hi}:
      Nat.add(Map.size(V, lo), Map.size(V, hi))

assert Map.to_list.go:
  forall -V: Type
  forall m: Map<V>
  forall acc: List<(String & V)>
  List<(String & V)>

def Map.to_list.go(V, m, acc):
  match m:
    case MTip{}:
      acc
    case MLeaf{k, v}:
      Con{(k, v), acc}
    case MNode{pos, lo, hi}:
      Map.to_list.go(V, lo, Map.to_list.go(V, hi, acc))

# the entries in code-point key order
assert Map.to_list:
  forall -V: Type
  forall m: Map<V>
  List<(String & V)>

def Map.to_list(V, m):
  Map.to_list.go(V, m, Nil{})

assert Map.keys.go:
  forall -V: Type
  forall m: Map<V>
  forall acc: List<String>
  List<String>

def Map.keys.go(V, m, acc):
  match m:
    case MTip{}:
      acc
    case MLeaf{k, v}:
      Con{k, acc}
    case MNode{pos, lo, hi}:
      Map.keys.go(V, lo, Map.keys.go(V, hi, acc))

# the keys in code-point order
assert Map.keys:
  forall -V: Type
  forall m: Map<V>
  List<String>

def Map.keys(V, m):
  Map.keys.go(V, m, Nil{})

assert Map.values.go:
  forall -V: Type
  forall m: Map<V>
  forall acc: List<V>
  List<V>

def Map.values.go(V, m, acc):
  match m:
    case MTip{}:
      acc
    case MLeaf{k, v}:
      Con{v, acc}
    case MNode{pos, lo, hi}:
      Map.values.go(V, lo, Map.values.go(V, hi, acc))

# the values in code-point key order
assert Map.values:
  forall -V: Type
  forall m: Map<V>
  List<V>

def Map.values(V, m):
  Map.values.go(V, m, Nil{})

assert Map.from_list.go:
  forall -V: Type
  forall kvs: List<(String & V)>
  forall m: Map<V>
  Map<V>

def Map.from_list.go(V, kvs, m):
  match kvs:
    case Nil{}:
      m
    case Con{kv, t}:
      Map.from_list.go(V, t, Map.set.kv(V, m, kv))

# later entries win on repeated keys, consistent with set
assert Map.from_list:
  forall -V: Type
  forall kvs: List<(String & V)>
  Map<V>

def Map.from_list(V, kvs):
  Map.from_list.go(V, kvs, MTip{})

# right-biased: b's entries are set into a, so b wins on shared keys
assert Map.union:
  forall -V: Type
  forall a: Map<V>
  forall b: Map<V>
  Map<V>

def Map.union(V, a, b):
  Map.from_list.go(V, Map.to_list(V, b), a)

# the boundary laws: the empty map answers every read with its
# default, is union's right unit, counts zero entries, and to_list /
# from_list agree on it -- each closes by reduction. The
# key-comparing family (get after set and kin) waits on theorems the
# affine walk keeps stuck at open keys.

assert Map.get_new:
  forall -V: Type
  forall cp: V -> (V & V)
  forall d: V
  forall key: String
  {Map.get(V, cp, d, Map.new(V), key) == (Map.new(V), d) : Map<V> & V}

def Map.get_new(V, cp, d, key):
  {==}

assert Map.has_new:
  forall -V: Type
  forall key: String
  {Map.has(V, Map.new(V), key) == (Map.new(V), False{}) : Map<V> & Bool}

def Map.has_new(V, key):
  {==}

assert Map.pop_new:
  forall -V: Type
  forall key: String
  {Map.pop(V, Map.new(V), key) == (Map.new(V), None{}) : Map<V> & Maybe<V>}

def Map.pop_new(V, key):
  {==}

assert Map.del_new:
  forall -V: Type
  forall key: String
  {Map.del(V, Map.new(V), key) == Map.new(V) : Map<V>}

def Map.del_new(V, key):
  {==}

assert Map.union_new:
  forall -V: Type
  forall m: Map<V>
  {Map.union(V, m, Map.new(V)) == m : Map<V>}

def Map.union_new(V, m):
  {==}

assert Map.size_new:
  forall -V: Type
  {Map.size(V, Map.new(V)) == 0n : Nat}

def Map.size_new(V):
  {==}

assert Map.to_list_new:
  forall -V: Type
  {Map.to_list(V, Map.new(V)) == Nil{} : List<(String & V)>}

def Map.to_list_new(V):
  {==}

assert Map.from_list_nil:
  forall -V: Type
  {Map.from_list(V, Nil{}) == Map.new(V) : Map<V>}

def Map.from_list_nil(V):
  {==}

# Set
# ===
# Not a machinery of its own -- Set IS Map<Unit>, the same move that
# makes String a list of chars: a key is present exactly when it maps
# to Unit{}, so the crit-bit tree, its ordering and its costs all
# come from Map, and every def here is a wrapper redirecting there.
# add is the set domain's word for insert; to_list projects the keys,
# in code-point order; inter and diff walk one side's keys and test
# the other.

assert Set:
  Type

def Set():
  Map<Unit>

assert Set.new:
  Set()

def Set.new():
  Map.new(Unit)

assert Set.add:
  forall s: Set()
  forall key: String
  Set()

def Set.add(s, key):
  Map.set(Unit, s, key, Unit{})

assert Set.has:
  forall s: Set()
  forall key: String
  Set() & Bool

def Set.has(s, key):
  Map.has(Unit, s, key)

assert Set.del:
  forall s: Set()
  forall key: String
  Set()

def Set.del(s, key):
  Map.del(Unit, s, key)

# right-biased like Map's, invisible here: every value is Unit{}
assert Set.union:
  forall a: Set()
  forall b: Set()
  Set()

def Set.union(a, b):
  Map.union(Unit, a, b)

assert Set.size:
  forall s: Set()
  Nat

def Set.size(s):
  Map.size(Unit, s)

# the members in code-point order
assert Set.to_list:
  forall s: Set()
  List<String>

def Set.to_list(s):
  Map.keys(Unit, s)

assert Set.from_list.go:
  forall ks: List<String>
  forall s: Set()
  Set()

def Set.from_list.go(ks, s):
  match ks:
    case Nil{}:
      s
    case Con{k, t}:
      Set.from_list.go(t, Map.set(Unit, s, k, Unit{}))

assert Set.from_list:
  forall ks: List<String>
  Set()

def Set.from_list(ks):
  Set.from_list.go(ks, Map.new(Unit))

assert Set.inter.go:
  forall ks: List<String>
  forall b: Set()
  forall acc: Set()
  Set()

def Set.inter.go(ks, b, acc):
  match ks:
    case Nil{}:
      acc
    case Con{k, t}:
      (k1, k2) = String.copy(k)
      (b2, hit) = Map.has(Unit, b, k1)
      match hit:
        case False{}:
          Set.inter.go(t, b2, acc)
        case True{}:
          Set.inter.go(t, b2, Map.set(Unit, acc, k2, Unit{}))

# the members of a that b also holds
assert Set.inter:
  forall a: Set()
  forall b: Set()
  Set()

def Set.inter(a, b):
  Set.inter.go(Map.keys(Unit, a), b, Map.new(Unit))

assert Set.diff.go:
  forall ks: List<String>
  forall b: Set()
  forall acc: Set()
  Set()

def Set.diff.go(ks, b, acc):
  match ks:
    case Nil{}:
      acc
    case Con{k, t}:
      (k1, k2) = String.copy(k)
      (b2, hit) = Map.has(Unit, b, k1)
      match hit:
        case False{}:
          Set.diff.go(t, b2, Map.set(Unit, acc, k2, Unit{}))
        case True{}:
          Set.diff.go(t, b2, acc)

# the members of a that b lacks
assert Set.diff:
  forall a: Set()
  forall b: Set()
  Set()

def Set.diff(a, b):
  Set.diff.go(Map.keys(Unit, a), b, Map.new(Unit))

# the boundary laws in set vocabulary: the empty set has nothing,
# absorbs into union, and annihilates inter and diff -- each closes
# by reduction

assert Set.has_new:
  forall key: String
  {Set.has(Set.new(), key) == (Set.new(), False{}) : Set() & Bool}

def Set.has_new(key):
  {==}

assert Set.del_new:
  forall key: String
  {Set.del(Set.new(), key) == Set.new() : Set()}

def Set.del_new(key):
  {==}

assert Set.to_list_new:
  {Set.to_list(Set.new()) == Nil{} : List<String>}

def Set.to_list_new():
  {==}

assert Set.union_new:
  forall s: Set()
  {Set.union(s, Set.new()) == s : Set()}

def Set.union_new(s):
  {==}

assert Set.new_inter:
  forall b: Set()
  {Set.inter(Set.new(), b) == Set.new() : Set()}

def Set.new_inter(b):
  {==}

assert Set.new_diff:
  forall b: Set()
  {Set.diff(Set.new(), b) == Set.new() : Set()}

def Set.new_diff(b):
  {==}
