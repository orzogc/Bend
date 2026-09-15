# The proofs of the typed evaluator's laws. opt_sound is an induction
# over the program: the literal cases close by conversion, and each
# compound case rewrites the induction hypotheses of its subterms
# into the goal and ends on a lemma about its folder. A folder lemma
# opens the folded subterm: the literal arm computes on both sides,
# and every other arm rebuilds the node, so both sides are the same
# evaluation. The Add and IsZero cases first rewrite the Ford
# equation and its index to TNum/TBool and {==}, so the folder and
# the evaluator compute.
#
# opt_complete is the same induction with a stronger claim: opt(e)
# is lit(eval(e)). Each compound case rewrites its subterms' opt into
# literals through the induction hypotheses; the folder then computes
# on literals, and the Add and IsZero cases close by conversion. The
# If case ends on lit_pick: a fold_if on a literal condition is the
# literal of the branch pick chooses. opt_idem is again an induction
# over the program: the subterms of a known object type are literals
# by opt_complete, so the folder computes on them; the branches of an
# If keep the open type t, so they use the induction hypothesis
# through fold_if_idem. No case needs the type t live, so t stays
# erased and the recursion is structural on the program alone.
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

# Completeness
# ------------

# LAW: a fold_if on a literal condition is the literal of the branch
# that pick chooses.
law lit_pick:
  for -t: TE.Ty
  for v: Bool
  for -x: TE.Val(t)
  for -y: TE.Val(t)
  {TE.lit(t, TE.pick(t, v, x, y)) == TE.fold_if(t, TE.Bit{v, {==}}, TE.lit(t, x), TE.lit(t, y)) : TE.Expr<t>}

def lit_pick(t, v, x, y):
  match v:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.opt_complete(t, e):
  match e:
    case TE.Num{n, eq}:
      %E@eq : {TE.lit(_, TE.eval(_, TE.Num{n, E})) == TE.opt(_, TE.Num{n, E}) : TE.Expr<_>}
      {==}
    case TE.Bit{b, eq}:
      %E@eq : {TE.lit(_, TE.eval(_, TE.Bit{b, E})) == TE.opt(_, TE.Bit{b, E}) : TE.Expr<_>}
      {==}
    case TE.Add{+a, +b, eq}:
      %E@eq : {TE.lit(_, TE.eval(_, TE.Add{a, b, E})) == TE.opt(_, TE.Add{a, b, E}) : TE.Expr<_>}
      %Laws.opt_complete(TE.TNum{}, a) : {TE.Num{Nat.add(TE.eval(TE.TNum{}, a), TE.eval(TE.TNum{}, b)), {==}} == TE.fold_add(_, TE.opt(TE.TNum{}, b)) : TE.Expr<TE.TNum{}>}
      %Laws.opt_complete(TE.TNum{}, b) : {TE.Num{Nat.add(TE.eval(TE.TNum{}, a), TE.eval(TE.TNum{}, b)), {==}} == TE.fold_add(TE.Num{TE.eval(TE.TNum{}, a), {==}}, _) : TE.Expr<TE.TNum{}>}
      {==}
    case TE.IsZero{+a, eq}:
      %E@eq : {TE.lit(_, TE.eval(_, TE.IsZero{a, E})) == TE.opt(_, TE.IsZero{a, E}) : TE.Expr<_>}
      %Laws.opt_complete(TE.TNum{}, a) : {TE.Bit{TE.is_zero(TE.eval(TE.TNum{}, a)), {==}} == TE.fold_zero(_) : TE.Expr<TE.TBool{}>}
      {==}
    case TE.If{+c, +a, +b}:
      %Laws.opt_complete(TE.TBool{}, c) : {TE.lit(t, TE.pick(t, TE.eval(TE.TBool{}, c), TE.eval(t, a), TE.eval(t, b))) == TE.fold_if(t, _, TE.opt(t, a), TE.opt(t, b)) : TE.Expr<t>}
      %Laws.opt_complete(t, a) : {TE.lit(t, TE.pick(t, TE.eval(TE.TBool{}, c), TE.eval(t, a), TE.eval(t, b))) == TE.fold_if(t, TE.Bit{TE.eval(TE.TBool{}, c), {==}}, _, TE.opt(t, b)) : TE.Expr<t>}
      %Laws.opt_complete(t, b) : {TE.lit(t, TE.pick(t, TE.eval(TE.TBool{}, c), TE.eval(t, a), TE.eval(t, b))) == TE.fold_if(t, TE.Bit{TE.eval(TE.TBool{}, c), {==}}, TE.lit(t, TE.eval(t, a)), _) : TE.Expr<t>}
      lit_pick(t, TE.eval(TE.TBool{}, c), TE.eval(t, a), TE.eval(t, b))

# Idempotence
# -----------

# LAW: a fold_if on a literal condition is a fixed point of opt when
# both branches are.
law fold_if_idem:
  for -t: TE.Ty
  for v: Bool
  for -x: TE.Expr<t>
  for -y: TE.Expr<t>
  for hx: {TE.opt(t, x) == x : TE.Expr<t>}
  for hy: {TE.opt(t, y) == y : TE.Expr<t>}
  {TE.opt(t, TE.fold_if(t, TE.Bit{v, {==}}, x, y)) == TE.fold_if(t, TE.Bit{v, {==}}, x, y) : TE.Expr<t>}

def fold_if_idem(t, v, x, y, hx, hy):
  match v:
    case True{}:
      hx
    case False{}:
      hy

def Laws.opt_idem(t, e):
  match e:
    case TE.Num{_, _}:
      {==}
    case TE.Bit{_, _}:
      {==}
    case TE.Add{+a, +b, eq}:
      %E@eq : {TE.opt(_, TE.opt(_, TE.Add{a, b, E})) == TE.opt(_, TE.Add{a, b, E}) : TE.Expr<_>}
      %Laws.opt_complete(TE.TNum{}, a) : {TE.opt(TE.TNum{}, TE.fold_add(_, TE.opt(TE.TNum{}, b))) == TE.fold_add(_, TE.opt(TE.TNum{}, b)) : TE.Expr<TE.TNum{}>}
      %Laws.opt_complete(TE.TNum{}, b) : {TE.opt(TE.TNum{}, TE.fold_add(TE.Num{TE.eval(TE.TNum{}, a), {==}}, _)) == TE.fold_add(TE.Num{TE.eval(TE.TNum{}, a), {==}}, _) : TE.Expr<TE.TNum{}>}
      {==}
    case TE.IsZero{+a, eq}:
      %E@eq : {TE.opt(_, TE.opt(_, TE.IsZero{a, E})) == TE.opt(_, TE.IsZero{a, E}) : TE.Expr<_>}
      %Laws.opt_complete(TE.TNum{}, a) : {TE.opt(TE.TBool{}, TE.fold_zero(_)) == TE.fold_zero(_) : TE.Expr<TE.TBool{}>}
      {==}
    case TE.If{+c, +a, +b}:
      %Laws.opt_complete(TE.TBool{}, c) : {TE.opt(t, TE.fold_if(t, _, TE.opt(t, a), TE.opt(t, b))) == TE.fold_if(t, _, TE.opt(t, a), TE.opt(t, b)) : TE.Expr<t>}
      fold_if_idem(t, TE.eval(TE.TBool{}, c), TE.opt(t, a), TE.opt(t, b), Laws.opt_idem(t, a), Laws.opt_idem(t, b))
