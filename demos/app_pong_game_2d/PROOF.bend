# Pong -- the proofs. This file imports the game (as Game) and the
# claims (as Laws) and fills every law. The field invariant follows the
# step: the paddles through paddle_in (a subtraction never grows, a cap
# never exceeds its bound), the ball's flight through fly_fits (a
# subtraction stays under the bound; the forward guard is the bound
# itself, so its truth is transported into the goal), then move_in and
# push_in walk the two Maybe outcomes (wall, side) and pick_le settles
# the paddle bounce. The order lemmas (le_refl, le_succ, le_pred,
# sub_le) are inductions over Pong.le. esc_quits is an induction over
# the events before the Esc; the Key arm is general over the key's
# quit flag. The sanity laws compute.
import Base
import ./main.bend as Game
import ./LAWS.bend as Laws

# Order lemmas
# ------------

law le_refl:
  for n: Nat
  Game.Pong.truth(Game.Pong.le(n, n))

def le_refl(n):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      le_refl(p)

law le_succ:
  for a: Nat
  for b: Nat
  for h: Game.Pong.truth(Game.Pong.le(a, b))
  Game.Pong.truth(Game.Pong.le(a, 1n+b))

def le_succ(a, b, h):
  match a:
    case 0n:
      Unit{}
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd(Game.Pong.truth(Game.Pong.le(p, 0n)), h)
        case 1n+q:
          le_succ(p, q, h)

law le_pred:
  for p: Nat
  for hi: Nat
  for h: Game.Pong.truth(Game.Pong.le(1n+p, hi))
  Game.Pong.truth(Game.Pong.le(p, hi))

def le_pred(p, hi, h):
  match hi:
    case 0n:
      Empty.absurd(Game.Pong.truth(Game.Pong.le(p, 0n)), h)
    case 1n+q:
      le_succ(p, q, h)

law sub_le:
  for p: Nat
  for k: Nat
  for +hi: Nat
  for h: Game.Pong.truth(Game.Pong.le(p, hi))
  Game.Pong.truth(Game.Pong.le(Nat.sub(p, k), hi))

def sub_le(p, k, hi, h):
  match p k:
    case 0n 0n:
      Unit{}
    case 0n 1n+kp:
      Unit{}
    case 1n++pp 0n:
      h
    case 1n++pp 1n+kp:
      sub_le(pp, kp, hi, le_pred(pp, hi, h))

# The paddles
# -----------

law cap_le_c:
  for c: Bool
  for +n: Nat
  for +hi: Nat
  for e: {c == Game.Pong.le(n, hi) : Bool}
  Game.Pong.truth(Game.Pong.le(Game.Pong.pick(c, n, hi), hi))

def cap_le_c(c, n, hi, e):
  match c:
    case True{}:
      %e : Game.Pong.truth(_)
      Unit{}
    case False{}:
      le_refl(hi)

law cap_le:
  for +n: Nat
  for +hi: Nat
  Game.Pong.truth(Game.Pong.le(Game.Pong.cap(n, hi), hi))

def cap_le(n, hi):
  cap_le_c(Game.Pong.le(n, hi), n, hi, {==})

law paddle_in:
  for +y: Nat
  for up: Bool
  for down: Bool
  for h: Game.Pong.truth(Game.Pong.le(y, 416n))
  Game.Pong.truth(Game.Pong.le(Game.Pong.paddle(y, up, down), 416n))

def paddle_in(y, up, down, h):
  match up down:
    case True{} False{}:
      sub_le(y, 6n, 416n, h)
    case False{} True{}:
      cap_le(Nat.add(y, 6n), 416n)
    case True{} True{}:
      h
    case False{} False{}:
      h

# The ball's flight
# -----------------
# fits(m, hi): a Some outcome is under the bound.

def fits(m: Maybe<Nat>, hi: Nat) -> Data:
  match m:
    case None{}:
      Unit
    case Some{q}:
      Game.Pong.truth(Game.Pong.le(q, hi))

law some_fits:
  for c: Bool
  for v: Nat
  for hi: Nat
  for hv: Game.Pong.truth(Game.Pong.le(v, hi))
  fits(Game.Pong.some_if(c, v), hi)

def some_fits(c, v, hi, hv):
  match c:
    case True{}:
      hv
    case False{}:
      Unit{}

law guard_fits:
  for c: Bool
  for v: Nat
  for hi: Nat
  for e: {c == Game.Pong.le(v, hi) : Bool}
  fits(Game.Pong.some_if(c, v), hi)

def guard_fits(c, v, hi, e):
  match c:
    case True{}:
      %e : Game.Pong.truth(_)
      Unit{}
    case False{}:
      Unit{}

law fly_fits:
  for dir: Bool
  for +p: Nat
  for hp: Game.Pong.truth(Game.Pong.le(p, 504n))
  fits(Game.Pong.fly(dir, p), 504n)

def fly_fits(dir, p, hp):
  match dir:
    case False{}:
      some_fits(Game.Pong.le(3n, p), Nat.sub(p, 3n), 504n,
        sub_le(p, 3n, 504n, hp))
    case True{}:
      guard_fits(Game.Pong.le(Nat.add(p, 3n), 504n), Nat.add(p, 3n), 504n, {==})

# The step
# --------

law pick_le:
  for c: Bool
  for a: Nat
  for b: Nat
  for hi: Nat
  for ha: Game.Pong.truth(Game.Pong.le(a, hi))
  for hb: Game.Pong.truth(Game.Pong.le(b, hi))
  Game.Pong.truth(Game.Pong.le(Game.Pong.pick(c, a, b), hi))

def pick_le(c, a, b, hi, ha, hb):
  match c:
    case True{}:
      ha
    case False{}:
      hb

law push_in:
  for +ly: Nat
  for +ry: Nat
  for keys: Game.Pong.Keys
  for +bx: Nat
  for +by: Nat
  for +dx: Bool
  for dy: Bool
  for mx: Maybe<Nat>
  for hl: Game.Pong.truth(Game.Pong.le(ly, 416n))
  for hr: Game.Pong.truth(Game.Pong.le(ry, 416n))
  for hx: Game.Pong.truth(Game.Pong.le(bx, 504n))
  for hy: Game.Pong.truth(Game.Pong.le(by, 504n))
  for fx: fits(mx, 504n)
  Game.Pong.in_field(Game.Pong.push(Game.Pong{ly, ry, keys, bx, by, dx, dy}, mx))

def push_in(ly, ry, keys, bx, by, dx, dy, mx, hl, hr, hx, hy, fx):
  match mx:
    case None{}:
      (hl, hr, Unit{}, Unit{})
    case Some{+bx2}:
      (hl, hr,
        pick_le(Game.Pong.catch(dx, bx2, by, ly, ry), bx, bx2, 504n, hx, fx),
        hy)

law move_in:
  for +ly: Nat
  for +ry: Nat
  for keys: Game.Pong.Keys
  for +bx: Nat
  for +by: Nat
  for +dx: Bool
  for dy: Bool
  for my: Maybe<Nat>
  for mx: Maybe<Nat>
  for hl: Game.Pong.truth(Game.Pong.le(ly, 416n))
  for hr: Game.Pong.truth(Game.Pong.le(ry, 416n))
  for hx: Game.Pong.truth(Game.Pong.le(bx, 504n))
  for hy: Game.Pong.truth(Game.Pong.le(by, 504n))
  for fy: fits(my, 504n)
  for fx: fits(mx, 504n)
  Game.Pong.in_field(
    Game.Pong.move(Game.Pong{ly, ry, keys, bx, by, dx, dy}, my, mx))

def move_in(ly, ry, keys, bx, by, dx, dy, my, mx, hl, hr, hx, hy, fy, fx):
  match my:
    case None{}:
      push_in(ly, ry, keys, bx, by, dx, Bool.not(dy), mx, hl, hr, hx, hy, fx)
    case Some{by2}:
      push_in(ly, ry, keys, bx, by2, dx, dy, mx, hl, hr, hx, fy, fx)

law step_fields:
  for +ly: Nat
  for +ry: Nat
  for keys: Game.Pong.Keys
  for +bx: Nat
  for +by: Nat
  for +dx: Bool
  for +dy: Bool
  for hl: Game.Pong.truth(Game.Pong.le(ly, 416n))
  for hr: Game.Pong.truth(Game.Pong.le(ry, 416n))
  for +hx: Game.Pong.truth(Game.Pong.le(bx, 504n))
  for +hy: Game.Pong.truth(Game.Pong.le(by, 504n))
  Game.Pong.in_field(Game.Pong.step(Game.Pong{ly, ry, keys, bx, by, dx, dy}))

def step_fields(ly, ry, keys, bx, by, dx, dy, hl, hr, hx, hy):
  match keys:
    case Game.Keys{+w, +s, +up, +down}:
      move_in(Game.Pong.paddle(ly, w, s), Game.Pong.paddle(ry, up, down),
        Game.Keys{w, s, up, down}, bx, by, dx, dy,
        Game.Pong.fly(dy, by), Game.Pong.fly(dx, bx),
        paddle_in(ly, w, s, hl), paddle_in(ry, up, down, hr), hx, hy,
        fly_fits(dy, by, hy), fly_fits(dx, bx, hx))

def Laws.step_in_field(g, h):
  match g:
    case Game.Pong{ly, ry, keys, bx, by, dx, dy}:
      (hl, hr, hx, hy) = h
      step_fields(ly, ry, keys, bx, by, dx, dy, hl, hr, hx, hy)

# Esc anywhere
# ------------

law esc_arm:
  for b: Bool
  for g: Game.Pong
  for -rest: List<Event>
  for ih: @s: Game.Pong -> {Game.Pong.events(rest, s) == None{} : Maybe<Game.Pong>}
  {Maybe.bind(&1, Game.Pong, Game.Pong, Game.Pong.quit(b, g),
      s => Game.Pong.events(rest, s)) == None{} : Maybe<Game.Pong>}

def esc_arm(b, g, rest, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih(g)

def Laws.esc_quits(pre, post, g):
  match pre:
    case Nil{}:
      match g:
        case Game.Pong{ly, ry, keys, bx, by, dx, dy}:
          {==}
    case Key{+code, +down} <> rest:
      match g:
        case Game.Pong{ly, ry, keys, bx, by, dx, dy}:
          esc_arm(Game.Pong.esc(code, down),
            Game.Pong{ly, ry, Game.Pong.press(down, code, keys), bx, by, dx, dy},
            Game.Pong.cat(rest, Key{27, True{}} <> post),
            s => Laws.esc_quits(rest, post, s))
    case Mouse{x, y, button, down} <> rest:
      Laws.esc_quits(rest, post, g)
    case Move{x, y} <> rest:
      Laws.esc_quits(rest, post, g)
    case Close{} <> rest:
      {==}

# Sanity
# ------

def Laws.init_in_field():
  (Unit{}, Unit{}, Unit{}, Unit{})

def Laws.first_step():
  {==}

def Laws.keys_lens(w, s, up, down):
  {==}
