# Pong: two paddles, a ball and walls, over base's App and Window kit.
# W/S move the left paddle, Up/Down (63232, 63233) the right; Esc or
# the close button quits. The state is a flat Data record: the paddles'
# tops and the ball's corner are Nats on a 512 x 512 field (a paddle is
# 8 x 96 and stays in 0..416, the ball 8 x 8 in 0..504), the held keys
# are four Bools, and the ball flies 3 pixels per frame along two
# direction Bools (True: right, or down). At a wall or a paddle the ball
# keeps its place and flips that direction; past a side it returns to
# the centre. The drawing reads the Nats as U32 words once per frame
# (Pong.scene), so LAWS.bend can speak about any state. A frame is an
# Image quadtree: draw classifies each quadrant against the three
# sprites and emits one Pix the moment the quadrant is uniform, so a
# 512 x 512 frame costs a few hundred nodes; the caller classifies the
# child (Pong.code) so the recursion is one def descending on the depth.
# The Spec section names what the laws say: the order on Nat, the field,
# and the join of two event lists.
#
#   bend demos/app_pong_game_2d/main.bend -o pong_game && ./pong_game
import Base

type Pong.Keys is Data:
  Keys{w: Bool, s: Bool, up: Bool, down: Bool}

type Pong is Data:
  Pong{ly: Nat, ry: Nat, keys: Pong.Keys, bx: Nat, by: Nat, dx: Bool, dy: Bool}

type Pong.Scene is Data:
  Scene{ly: U32, ry: U32, bx: U32, by: U32}

def Pong.init() -> Pong:
  Pong{208n, 208n, Keys{False{}, False{}, False{}, False{}}, 252n, 252n,
    True{}, True{}}

def Pong.pick(c: Bool, a: Nat, b: Nat) -> Nat:
  match c:
    case True{}:
      a
    case False{}:
      b

# Keys
# ----

def Pong.set(on: Bool, down: Bool, old: Bool) -> Bool:
  match on:
    case True{}:
      down
    case False{}:
      old

def Pong.press(+down: Bool, +code: U32, keys: Pong.Keys) -> Pong.Keys:
  Keys{w, s, up, dn} = keys
  Keys{Pong.set(U32.is_eq(code, 119), down, w),
    Pong.set(U32.is_eq(code, 115), down, s),
    Pong.set(U32.is_eq(code, 63232), down, up),
    Pong.set(U32.is_eq(code, 63233), down, dn)}

def Pong.esc(+code: U32, down: Bool) -> Bool:
  Bool.and(down, U32.is_eq(code, 27))

def Pong.quit(esc: Bool, g: Pong) -> Maybe<Pong>:
  match esc:
    case True{}:
      None{}
    case False{}:
      Some{g}

def Pong.key(+code: U32, +down: Bool, g: Pong) -> Maybe<Pong>:
  Pong{ly, ry, keys, bx, by, dx, dy} = g
  Pong.quit(Pong.esc(code, down),
    Pong{ly, ry, Pong.press(down, code, keys), bx, by, dx, dy})

def Pong.event(e: Event, g: Pong) -> Maybe<Pong>:
  match e:
    case Key{code, down}:
      Pong.key(code, down, g)
    case Mouse{x, y, button, down}:
      Some{g}
    case Move{x, y}:
      Some{g}
    case Close{}:
      None{}

def Pong.events(events: List<Event>, g: Pong) -> Maybe<Pong>:
  match events:
    case Nil{}:
      Some{g}
    case e <> rest:
      Maybe.bind(&1, Pong, Pong, Pong.event(e, g), g2 => Pong.events(rest, g2))

# Motion
# ------
# A paddle moves 6 pixels toward its held key and stops at the field's
# edge. The ball's next coordinate along one axis is fly: None past the
# field. move settles the vertical axis (a wall keeps by and flips dy),
# push the horizontal one (a side resets the ball; a paddle in reach
# keeps bx and flips dx).

def Pong.le(a: Nat, b: Nat) -> Bool:
  match a:
    case 0n:
      True{}
    case 1n+p:
      match b:
        case 0n:
          False{}
        case 1n+q:
          Pong.le(p, q)

def Pong.cap(+n: Nat, +hi: Nat) -> Nat:
  Pong.pick(Pong.le(n, hi), n, hi)

def Pong.paddle(y: Nat, up: Bool, down: Bool) -> Nat:
  match up down:
    case True{} False{}:
      Nat.sub(y, 6n)
    case False{} True{}:
      Pong.cap(Nat.add(y, 6n), 416n)
    case True{} True{}:
      y
    case False{} False{}:
      y

def Pong.some_if(c: Bool, v: Nat) -> Maybe<Nat>:
  match c:
    case True{}:
      Some{v}
    case False{}:
      None{}

def Pong.fly(dir: Bool, +p: Nat) -> Maybe<Nat>:
  match dir:
    case False{}:
      Pong.some_if(Pong.le(3n, p), Nat.sub(p, 3n))
    case True{}:
      Pong.some_if(Pong.le(Nat.add(p, 3n), 504n), Nat.add(p, 3n))

def Pong.overlap(+by: Nat, +py: Nat) -> Bool:
  Bool.and(Pong.le(py, Nat.add(by, 8n)), Pong.le(by, Nat.add(py, 96n)))

def Pong.catch(dx: Bool, +bx: Nat, +by: Nat, ly: Nat, ry: Nat) -> Bool:
  match dx:
    case False{}:
      Bool.and(Pong.le(bx, 16n), Pong.overlap(by, ly))
    case True{}:
      Bool.and(Pong.le(488n, bx), Pong.overlap(by, ry))

def Pong.push(+g: Pong, mx: Maybe<Nat>) -> Pong:
  Pong{ly, ry, keys, bx, by, dx, dy} = g
  match mx:
    case None{}:
      Pong{ly, ry, keys, 252n, 252n, True{}, True{}}
    case Some{+bx2}:
      +hit = Pong.catch(dx, bx2, by, ly, ry)
      Pong{ly, ry, keys, Pong.pick(hit, bx, bx2), by, Bool.xor(hit, dx), dy}

def Pong.move(+g: Pong, my: Maybe<Nat>, mx: Maybe<Nat>) -> Pong:
  Pong{ly, ry, keys, bx, by, dx, dy} = g
  match my:
    case None{}:
      Pong.push(Pong{ly, ry, keys, bx, by, dx, Bool.not(dy)}, mx)
    case Some{by2}:
      Pong.push(Pong{ly, ry, keys, bx, by2, dx, dy}, mx)

def Pong.step(+g: Pong) -> Pong:
  Pong{ly, ry, keys, bx, by, dx, dy} = g
  Keys{w, s, up, down} = keys
  Pong.move(
    Pong{Pong.paddle(ly, w, s), Pong.paddle(ry, up, down), keys, bx, by, dx, dy},
    Pong.fly(dy, by), Pong.fly(dx, bx))

def Pong.after(m: Maybe<Pong>) -> Maybe<Pong>:
  match m:
    case None{}:
      None{}
    case Some{g}:
      Some{Pong.step(g)}

def Pong.tick(events: List<Event>, g: Pong) -> IO(Maybe<Pong>):
  IO.pure(Maybe<Pong>, Pong.after(Pong.events(events, g)))

# Draw
# ----

def Pong.hit_in(out: Bool, in: Bool) -> U32:
  match out in:
    case True{} _:
      0
    case False{} True{}:
      2
    case False{} False{}:
      1

def Pong.hit(+x0: U32, +y0: U32, +s: U32, +rx: U32, +ry: U32, +rw: U32, +rh: U32)
  -> U32:
  Pong.hit_in(
    ((x0 + s <= rx) || (rx + rw <= x0) || (y0 + s <= ry) || (ry + rh <= y0)
      : U32),
    ((rx <= x0) && (x0 + s <= rx + rw) && (ry <= y0) && (y0 + s <= ry + rh)
      : U32))

def Pong.code_of(ball: Bool, pad: Bool, none: Bool) -> Nat:
  match ball pad none:
    case True{} _ _:
      1n
    case False{} True{} _:
      2n
    case False{} False{} True{}:
      0n
    case False{} False{} False{}:
      3n

def Pong.code(d: Nat, +x0: U32, +y0: U32, +sc: Pong.Scene) -> Nat:
  Scene{ly, ry, bx, by} = sc
  +s = U32.shln(1, d)
  +hb = Pong.hit(x0, y0, s, bx, by, 8, 8)
  +hl = Pong.hit(x0, y0, s, 8, ly, 8, 96)
  +hr = Pong.hit(x0, y0, s, 496, ry, 8, 96)
  Pong.code_of(U32.is_eq(hb, 2),
    (U32.is_eq(hl, 2) || U32.is_eq(hr, 2)) && U32.is_eq(hb, 0),
    U32.is_eq((hb + hl + hr : U32), 0))

def Pong.color(code: Nat) -> U32:
  match code:
    case 0n:
      0
    case 1n:
      16763904
    case _:
      16777215

def Pong.draw(+d: Nat, code: Nat, +x0: U32, +y0: U32, +sc: Pong.Scene) -> Image:
  match d:
    case 0n:
      Pix{Pong.color(code)}
    case 1n+e:
      match code:
        case 0n:
          Pix{0}
        case 1n:
          Pix{16763904}
        case 2n:
          Pix{16777215}
        case _:
          +h = U32.shln(1, e)
          +x1 = U32.add(x0, h)
          +y1 = U32.add(y0, h)
          tl tr bl br = Pong.draw(e, Pong.code(e, x0, y0, sc), x0, y0, sc)
            Pong.draw(e, Pong.code(e, x1, y0, sc), x1, y0, sc)
            Pong.draw(e, Pong.code(e, x0, y1, sc), x0, y1, sc)
            Pong.draw(e, Pong.code(e, x1, y1, sc), x1, y1, sc)
          Qua{tl, tr, bl, br}

def Pong.scene(g: Pong) -> Pong.Scene:
  Pong{ly, ry, keys, bx, by, dx, dy} = g
  Scene{U32.from_nat(ly), U32.from_nat(ry), U32.from_nat(bx), U32.from_nat(by)}

def Pong.view(g: Pong) -> Pong & Image:
  +g2 = g
  +sc = Pong.scene(g2)
  (g2, Pong.draw(9n, Pong.code(9n, 0, 0, sc), 0, 0, sc))

# Spec
# ----
# What LAWS.bend says about the game: the truth of a Bool as a type, the
# field (each paddle's top at most 416, the ball's corner at most 504
# on both axes), and cat, the join of two event lists.

def Pong.truth(b: Bool) -> Data:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def Pong.in_field(g: Pong) -> Type:
  Pong{ly, ry, keys, bx, by, dx, dy} = g
  Pong.truth(Pong.le(ly, 416n)) & Pong.truth(Pong.le(ry, 416n))
    & Pong.truth(Pong.le(bx, 504n)) & Pong.truth(Pong.le(by, 504n))

def Pong.cat(xs: List<Event>, ys: List<Event>) -> List<Event>:
  match xs:
    case Nil{}:
      ys
    case x <> rest:
      x <> Pong.cat(rest, ys)

def main() -> IO(Unit):
  App.run(~Pong, ~App{Pong.view, Pong.tick}, "Pong", 512, 512, Pong.init())
