# The laws of the typed evaluator. opt_sound is the headline: the
# constant folder keeps the meaning of every well-typed program, at
# every object type. The other laws pin the folder on the shapes it
# folds, and the value of the sample program. PROOF.bend must prove
# them.
import Base
import ./main.bend as TE

# LAW: the optimizer keeps the meaning of every program: for every
# object type t and every program e of that type, opt(e) evaluates
# to what e evaluates to.
law opt_sound:
  for -t: TE.Ty
  for e: TE.Expr<t>
  {TE.eval(t, TE.opt(t, e)) == TE.eval(t, e) : TE.Val(t)}

# LAW: the optimizer folds a sum of two literals into their sum.
law opt_folds_add:
  for x: Nat
  for y: Nat
  {TE.opt(TE.TNum{}, TE.Add{TE.Num{x, {==}}, TE.Num{y, {==}}, {==}}) == TE.Num{Nat.add(x, y), {==}} : TE.Expr<TE.TNum{}>}

# LAW: a branch on the literal true is the optimized then-branch,
# at every object type.
law opt_picks_then:
  for -t: TE.Ty
  for a: TE.Expr<t>
  for b: TE.Expr<t>
  {TE.opt(t, TE.If{TE.Bit{True{}, {==}}, a, b}) == TE.opt(t, a) : TE.Expr<t>}

# LAW: the sample program, if iszero (0 + 0) then 10 else 20, plus
# 3, evaluates to 13.
law sample_value:
  {TE.eval(TE.TNum{}, TE.sample()) == 13n : Nat}
