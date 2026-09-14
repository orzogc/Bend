# proof_typed_eval: an intrinsically-typed expression language. An
# Expr<t> is a program of object type t (TNum or TBool) that is
# well-typed by construction: each constructor carries an equation
# {TNum{} == t : Ty} (the Ford trick), so Bend checks the object
# program's types when it builds the term. eval maps an Expr<t> to
# Val(t), the meaning of t: it has no error case and no default.
# opt is a constant folder; LAWS.bend states that it keeps the
# meaning of every program. Try it:
#
#   bend demos/proof_typed_eval/main.bend
import Base

# Types
# -----

# The object language's types.
type Ty is Data:
  TNum{}
  TBool{}

# The meaning of a type: a Bend type.
def Val(t: Ty) -> Type:
  match t:
    case TNum{}:
      Nat
    case TBool{}:
      Bool

# Typed expressions. The eq field of a constructor pins t to the
# type it produces; If's branches share the type of the whole.
type Expr<-t: Ty> is Data:
  Num{n: Nat, eq: {TNum{} == t : Ty}}
  Bit{b: Bool, eq: {TBool{} == t : Ty}}
  Add{a: Expr<TNum{}>, b: Expr<TNum{}>, eq: {TNum{} == t : Ty}}
  IsZero{a: Expr<TNum{}>, eq: {TBool{} == t : Ty}}
  If{c: Expr<TBool{}>, a: Expr<t>, b: Expr<t>}

# Evaluation
# ----------

# Moves a value of type s to type u along the equation s == u. When
# the two types agree the value passes as it is; the two clash arms
# transport it along an equation that no program can build.
def cast(s: Ty, u: Ty, eq: {s == u : Ty}, v: Val(s)) -> Val(u):
  match s u:
    case TNum{} TNum{}:
      v
    case TBool{} TBool{}:
      v
    case TNum{} TBool{}:
      %eq : Val(_)
      v
    case TBool{} TNum{}:
      %eq : Val(_)
      v

def is_zero(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      False{}

# The meaning of If: a branch chosen by a Bool.
def pick(-t: Ty, b: Bool, x: Val(t), y: Val(t)) -> Val(t):
  match b:
    case True{}:
      x
    case False{}:
      y

# The evaluator's worker: one arm per constructor, no error case.
# The index t is erased, so the recursion is structural on e alone;
# u is a live copy of t (w ties them) that cast matches on to place
# each value in Val(u).
def eval.go(-t: Ty, e: Expr<t>, +u: Ty, +w: {t == u : Ty}) -> Val(u):
  match e:
    case Num{n, eq}:
      cast(TNum{}, u, Equal.trans(Ty, TNum{}, t, u, eq, w), n)
    case Bit{b, eq}:
      cast(TBool{}, u, Equal.trans(Ty, TBool{}, t, u, eq, w), b)
    case Add{a, b, eq}:
      cast(TNum{}, u, Equal.trans(Ty, TNum{}, t, u, eq, w), Nat.add(eval.go(TNum{}, a, TNum{}, {==}), eval.go(TNum{}, b, TNum{}, {==})))
    case IsZero{a, eq}:
      cast(TBool{}, u, Equal.trans(Ty, TBool{}, t, u, eq, w), is_zero(eval.go(TNum{}, a, TNum{}, {==})))
    case If{c, a, b}:
      pick(u, eval.go(TBool{}, c, TBool{}, {==}), eval.go(t, a, u, w), eval.go(t, b, u, w))

# The meaning of a program.
def eval(t: Ty, e: Expr<t>) -> Val(t):
  eval.go(t, e, t, {==})

# Constant folding
# ----------------

# A sum of two literals is a literal.
def fold_add(a: Expr<TNum{}>, b: Expr<TNum{}>) -> Expr<TNum{}>:
  match a b:
    case Num{x, _} Num{y, _}:
      Num{Nat.add(x, y), {==}}
    case a b:
      Add{a, b, {==}}

# A zero test of a literal is a literal.
def fold_zero(a: Expr<TNum{}>) -> Expr<TBool{}>:
  match a:
    case Num{n, _}:
      Bit{is_zero(n), {==}}
    case a:
      IsZero{a, {==}}

# A branch on a literal is the branch it picks.
def fold_if(-t: Ty, c: Expr<TBool{}>, a: Expr<t>, b: Expr<t>) -> Expr<t>:
  match c:
    case Bit{True{}, _}:
      a
    case Bit{False{}, _}:
      b
    case c:
      If{c, a, b}

# The optimizer: folds every subterm, then the node above it.
def opt(-t: Ty, e: Expr<t>) -> Expr<t>:
  match e:
    case Num{n, eq}:
      Num{n, eq}
    case Bit{b, eq}:
      Bit{b, eq}
    case Add{a, b, eq}:
      %eq : Expr<_>
      fold_add(opt(TNum{}, a), opt(TNum{}, b))
    case IsZero{a, eq}:
      %eq : Expr<_>
      fold_zero(opt(TNum{}, a))
    case If{c, a, b}:
      fold_if(t, opt(TBool{}, c), opt(t, a), opt(t, b))

# Main
# ----

# if iszero (0 + 0) then 10 else 20, plus 3. Every {==} is a typing
# fact that Bend checks: Num{0n, {==}} at type TBool would not build.
def sample() -> Expr<TNum{}>:
  Add{If{IsZero{Add{Num{0n, {==}}, Num{0n, {==}}, {==}}, {==}}, Num{10n, {==}}, Num{20n, {==}}}, Num{3n, {==}}, {==}}

def main() -> Nat:
  eval(TNum{}, sample())
