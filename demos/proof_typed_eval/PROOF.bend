# The proofs of the typed evaluator's laws. opt_sound is an induction
# over the program: the literal cases close by conversion, and each
# compound case rewrites the induction hypotheses of its subterms
# into the goal and ends on a lemma about its folder. A folder lemma
# opens the folded subterm: the literal arm computes on both sides,
# and every other arm rebuilds the node, so both sides are the same
# evaluation. The Add and IsZero cases first rewrite the Ford
# equation and its index to TNum/TBool and {==}, so the folder and
# the evaluator compute.
import Base
import ./main.bend as TE
import ./LAWS.bend as Laws

# Folder lemmas
# -------------

# LAW: folding a sum evaluates to the sum of the evaluations.
law fold_add_sound:
  for a: TE.Expr<TE.TNum{}>
  for b: TE.Expr<TE.TNum{}>
  {TE.eval(TE.TNum{}, TE.fold_add(a, b)) == Nat.add(TE.eval(TE.TNum{}, a), TE.eval(TE.TNum{}, b)) : Nat}

def fold_add_sound(a, b):
  match a b:
    case TE.Num{_, _} TE.Num{_, _}:
      {==}
    case TE.Num{_, _} TE.Bit{_, _}:
      {==}
    case TE.Num{_, _} TE.Add{_, _, _}:
      {==}
    case TE.Num{_, _} TE.IsZero{_, _}:
      {==}
    case TE.Num{_, _} TE.If{_, _, _}:
      {==}
    case TE.Bit{_, _} _:
      {==}
    case TE.Add{_, _, _} _:
      {==}
    case TE.IsZero{_, _} _:
      {==}
    case TE.If{_, _, _} _:
      {==}

# LAW: folding a zero test evaluates to the zero test of the
# evaluation.
law fold_zero_sound:
  for a: TE.Expr<TE.TNum{}>
  {TE.eval(TE.TBool{}, TE.fold_zero(a)) == TE.is_zero(TE.eval(TE.TNum{}, a)) : Bool}

def fold_zero_sound(a):
  match a:
    case TE.Num{_, _}:
      {==}
    case TE.Bit{_, _}:
      {==}
    case TE.Add{_, _, _}:
      {==}
    case TE.IsZero{_, _}:
      {==}
    case TE.If{_, _, _}:
      {==}

# LAW: folding a branch evaluates to the branch its condition picks.
law fold_if_sound:
  for -t: TE.Ty
  for c: TE.Expr<TE.TBool{}>
  for a: TE.Expr<t>
  for b: TE.Expr<t>
  {TE.eval(t, TE.fold_if(t, c, a, b)) == TE.pick(t, TE.eval(TE.TBool{}, c), TE.eval(t, a), TE.eval(t, b)) : TE.Val(t)}

def fold_if_sound(t, c, a, b):
  match c:
    case TE.Bit{True{}, _}:
      {==}
    case TE.Bit{False{}, _}:
      {==}
    case TE.Num{_, _}:
      {==}
    case TE.Add{_, _, _}:
      {==}
    case TE.IsZero{_, _}:
      {==}
    case TE.If{_, _, _}:
      {==}

# The laws
# --------

def Laws.opt_sound(t, e):
  match e:
    case TE.Num{_, _}:
      {==}
    case TE.Bit{_, _}:
      {==}
    case TE.Add{+a, +b, eq}:
      %E@eq : {TE.eval(_, TE.opt(_, TE.Add{a, b, E})) == TE.eval(_, TE.Add{a, b, E}) : TE.Val(_)}
      %Laws.opt_sound(TE.TNum{}, a) : {TE.eval(TE.TNum{}, TE.fold_add(TE.opt(TE.TNum{}, a), TE.opt(TE.TNum{}, b))) == Nat.add(_, TE.eval(TE.TNum{}, b)) : Nat}
      %Laws.opt_sound(TE.TNum{}, b) : {TE.eval(TE.TNum{}, TE.fold_add(TE.opt(TE.TNum{}, a), TE.opt(TE.TNum{}, b))) == Nat.add(TE.eval(TE.TNum{}, TE.opt(TE.TNum{}, a)), _) : Nat}
      fold_add_sound(TE.opt(TE.TNum{}, a), TE.opt(TE.TNum{}, b))
    case TE.IsZero{+a, eq}:
      %E@eq : {TE.eval(_, TE.opt(_, TE.IsZero{a, E})) == TE.eval(_, TE.IsZero{a, E}) : TE.Val(_)}
      %Laws.opt_sound(TE.TNum{}, a) : {TE.eval(TE.TBool{}, TE.fold_zero(TE.opt(TE.TNum{}, a))) == TE.is_zero(_) : Bool}
      fold_zero_sound(TE.opt(TE.TNum{}, a))
    case TE.If{+c, +a, +b}:
      %Laws.opt_sound(TE.TBool{}, c) : {TE.eval(t, TE.fold_if(t, TE.opt(TE.TBool{}, c), TE.opt(t, a), TE.opt(t, b))) == TE.pick(t, _, TE.eval(t, a), TE.eval(t, b)) : TE.Val(t)}
      %Laws.opt_sound(t, a) : {TE.eval(t, TE.fold_if(t, TE.opt(TE.TBool{}, c), TE.opt(t, a), TE.opt(t, b))) == TE.pick(t, TE.eval(TE.TBool{}, TE.opt(TE.TBool{}, c)), _, TE.eval(t, b)) : TE.Val(t)}
      %Laws.opt_sound(t, b) : {TE.eval(t, TE.fold_if(t, TE.opt(TE.TBool{}, c), TE.opt(t, a), TE.opt(t, b))) == TE.pick(t, TE.eval(TE.TBool{}, TE.opt(TE.TBool{}, c)), TE.eval(t, TE.opt(t, a)), _) : TE.Val(t)}
      fold_if_sound(t, TE.opt(TE.TBool{}, c), TE.opt(t, a), TE.opt(t, b))

def Laws.opt_folds_add(x, y):
  {==}

def Laws.opt_picks_then(t, a, b):
  {==}

def Laws.sample_value():
  {==}
