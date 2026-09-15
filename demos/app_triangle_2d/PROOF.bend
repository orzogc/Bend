# Triangle -- the proofs. This file imports the program (as App) and the
# claims (as Laws) and fills every law. replay is an induction over the
# event list with a case analysis on the head event: the Key and Mouse
# arms branch on a computed Bool (Esc? inside?), so each arm is a lemma
# general over that Bool, and the Mouse arm moves the click through
# Nat.add with add_succ; the empty list needs add_zero. esc_quits is the
# same induction over the events before the Esc. keeps is a case
# analysis on the event whose hypotheses are spent by rewrites, and the
# Close case is refuted (True is not False).
import Base
import ./main.bend as App
import ./LAWS.bend as Laws

# Nat lemmas
# ----------

law add_zero:
  for n: Nat
  {Nat.add(n, 0n) == n : Nat}

def add_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

law add_succ:
  for a: Nat
  for -b: Nat
  {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}

def add_succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# Bool reflection: the truth of a Bool as a type, so True == False is
# refuted by transport.
def T(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def disc(e: {True{} == False{} : Bool}) -> Empty:
  %e : T(_)
  Unit{}

# The replay
# ----------
# One frame's events, folded. The Key arm: the key's quit flag is a
# computed Bool, so the arm is general over it. The Mouse arm: the hit
# flag likewise; on a hit the count grows by one on the left of Nat.add
# and by one inside its right argument, which add_succ reconciles.

law key_arm:
  for b: Bool
  for n: Nat
  for -rest: List<Event>
  for ih: {App.Tri.events(rest, n)
    == App.Tri.quit(App.Tri.quits(rest), Nat.add(n, App.Tri.hits(rest)))
    : Maybe<Nat>}
  {Maybe.bind(&1, Nat, Nat, App.Tri.quit(b, n), m => App.Tri.events(rest, m))
    == App.Tri.quit(Bool.or(b, App.Tri.quits(rest)),
      Nat.add(n, App.Tri.hits(rest)))
    : Maybe<Nat>}

def key_arm(b, n, rest, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih

law mouse_arm:
  for h: Bool
  for +n: Nat
  for -rest: List<Event>
  for ih: @m: Nat -> {App.Tri.events(rest, m)
    == App.Tri.quit(App.Tri.quits(rest), Nat.add(m, App.Tri.hits(rest)))
    : Maybe<Nat>}
  {App.Tri.events(rest, App.Tri.bump(h, n))
    == App.Tri.quit(App.Tri.quits(rest),
      Nat.add(n, App.Tri.bump(h, App.Tri.hits(rest))))
    : Maybe<Nat>}

def mouse_arm(h, n, rest, ih):
  match h:
    case True{}:
      %add_succ(n, App.Tri.hits(rest))
        : {App.Tri.events(rest, 1n+n) == App.Tri.quit(App.Tri.quits(rest), _)
          : Maybe<Nat>}
      ih(1n+n)
    case False{}:
      ih(n)

def Laws.replay(evs, n):
  match evs:
    case Nil{}:
      %add_zero(n) : {Some{_} == Some{Nat.add(n, 0n)} : Maybe<Nat>}
      {==}
    case Key{code, down} <> rest:
      key_arm(App.Tri.esc(code, down), n, rest, Laws.replay(rest, n))
    case Mouse{x, y, button, down} <> rest:
      mouse_arm(Bool.and(down, App.Tri.inside(x, y)), n, rest,
        m => Laws.replay(rest, m))
    case Move{x, y} <> rest:
      Laws.replay(rest, n)
    case Close{} <> rest:
      {==}

# Esc anywhere
# ------------
# Induction over the events before the Esc: each keeps the frame alive
# with some count (or quits earlier, which is None too), and the Esc
# then quits from any count.

law esc_arm:
  for b: Bool
  for n: Nat
  for -rest: List<Event>
  for ih: @m: Nat -> {App.Tri.events(rest, m) == None{} : Maybe<Nat>}
  {Maybe.bind(&1, Nat, Nat, App.Tri.quit(b, n), m => App.Tri.events(rest, m))
    == None{} : Maybe<Nat>}

def esc_arm(b, n, rest, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih(n)

def Laws.esc_quits(pre, post, n):
  match pre:
    case Nil{}:
      {==}
    case Key{code, down} <> rest:
      esc_arm(App.Tri.esc(code, down), n,
        App.Tri.cat(rest, Key{27, True{}} <> post),
        m => Laws.esc_quits(rest, post, m))
    case Mouse{x, y, button, down} <> rest:
      Laws.esc_quits(rest, post,
        App.Tri.bump(Bool.and(down, App.Tri.inside(x, y)), n))
    case Move{x, y} <> rest:
      Laws.esc_quits(rest, post, n)
    case Close{} <> rest:
      {==}

# Keeping the count
# -----------------

def Laws.keeps(e, n, h, q):
  match e:
    case Key{code, down}:
      %Equal.sym(Bool, App.Tri.esc(code, down), False{}, q)
        : {App.Tri.quit(_, n) == Some{n} : Maybe<Nat>}
      {==}
    case Mouse{x, y, button, down}:
      %Equal.sym(Bool, Bool.and(down, App.Tri.inside(x, y)), False{}, h)
        : {Some{App.Tri.bump(_, n)} == Some{n} : Maybe<Nat>}
      {==}
    case Move{x, y}:
      {==}
    case Close{}:
      Empty.absurd({App.Tri.event(Close{}, n) == Some{n} : Maybe<Nat>}, disc(q))

def Laws.click_inside(n):
  {==}
