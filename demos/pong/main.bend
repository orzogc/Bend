# Pong: two paddles, a ball and walls, over base's App and Window kit.
# W/S move the left paddle, Up/Down the right; Esc or the close button
# quits. The state is a flat Data record of words: the held keys are
# bits of one word (1 W, 2 S, 4 Up, 8 Down), speeds wrap (a "negative"
# speed is 2^32 - k), so a coordinate past 2^31 reads as an off-field
# wrap. A frame is an Image quadtree: draw classifies each quadrant
# against the three sprites and emits one Pix the moment the quadrant
# is uniform, so a 512 x 512 frame costs a few hundred nodes, not
# 262144; the caller classifies the child (Pong.code) so the recursion
# is one def descending on the depth.
#
#   bend demos/pong/main.bend -o pong && ./pong
import Base

type Pong is Data:
  Pong{ly: U32, ry: U32, held: U32, bx: U32, by: U32, vx: U32, vy: U32}

def Pong.init() -> Pong:
  Pong{208, 208, 0, 252, 252, 3, 3}

def Pong.bit(b: Bool, v: U32) -> U32:
  match b:
    case True{}:
      v
    case False{}:
      0

def Pong.pick(c: Bool, a: U32, b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

def Pong.mask(+code: U32) -> U32:
  (Pong.bit(U32.is_eq(code, 119), 1) .|. Pong.bit(U32.is_eq(code, 115), 2)
    .|. Pong.bit(U32.is_eq(code, 130), 4) .|. Pong.bit(U32.is_eq(code, 131), 8)
    : U32)

def Pong.press(down: Bool, held: U32, mask: U32) -> U32:
  match down:
    case True{}:
      (held .|. mask : U32)
    case False{}:
      (held .&. U32.not(mask) : U32)

def Pong.quit(esc: Bool, g: Pong) -> Maybe<Pong>:
  match esc:
    case True{}:
      None{}
    case False{}:
      Some{g}

def Pong.key(+code: U32, +down: Bool, g: Pong) -> Maybe<Pong>:
  Pong{ly, ry, held, bx, by, vx, vy} = g
  Pong.quit(Bool.and(down, U32.is_eq(code, 27)),
    Pong{ly, ry, Pong.press(down, held, Pong.mask(code)), bx, by, vx, vy})

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
    case Con{e, rest}:
      Maybe.bind(&1, Pong, Pong, Pong.event(e, g), g2 => Pong.events(rest, g2))

def Pong.clamp(neg: Bool, +y: U32) -> U32:
  match neg:
    case True{}:
      0
    case False{}:
      Pong.pick((y > 416 : U32), 416, y)

def Pong.paddle(+y: U32, +held: U32, up: U32, down: U32) -> U32:
  +y2 = (y - 6 * (held .&. up) + 6 * (held .&. down) : U32)
  Pong.clamp((y2 > 2147483647 : U32), y2)

def Pong.overlap(+by: U32, +py: U32) -> Bool:
  ((by + 8 >= py) && (by <= py + 96) : U32)

def Pong.bounce(hit: Bool, +v: U32) -> U32:
  match hit:
    case True{}:
      (0 - v : U32)
    case False{}:
      v

def Pong.reset(out: Bool, g: Pong) -> Pong:
  match out:
    case True{}:
      Pong{ly, ry, held, bx, by, vx, vy} = g
      Pong{ly, ry, held, 252, 252, 3, 3}
    case False{}:
      g

def Pong.step(+g: Pong) -> Pong:
  Pong{ly, ry, held, bx, by, vx, vy} = g
  +ly2 = Pong.paddle(ly, held, 1, (held >> 1n .&. 1 : U32))
  +ry2 = Pong.paddle(ry, held, (held >> 2n .&. 1 : U32), (held >> 3n .&. 1 : U32))
  +by2 = (by + vy : U32)
  +wall = ((by2 > 2147483647) || (by2 > 504) : U32)
  +bx2 = (bx + vx : U32)
  +left = (vx > 2147483647 : U32)
  +hit = (left && (bx2 <= 16) && Pong.overlap(by2, ly2)
    || Bool.not(left) && (bx2 + 8 >= 496) && Pong.overlap(by2, ry2) : U32)
  +bx3 = Pong.pick(hit, bx, bx2)
  Pong.reset(((bx3 > 2147483647) || (bx3 > 504) : U32),
    Pong{ly2, ry2, held, bx3, Pong.pick(wall, by, by2), Pong.bounce(hit, vx),
      Pong.bounce(wall, vy)})

def Pong.after(m: Maybe<Pong>) -> Maybe<Pong>:
  match m:
    case None{}:
      None{}
    case Some{g}:
      Some{Pong.step(g)}

def Pong.tick(events: List<Event>, g: Pong) -> Maybe<Pong>:
  Pong.after(Pong.events(events, g))

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

def Pong.code(d: Nat, +x0: U32, +y0: U32, +g: Pong) -> Nat:
  Pong{ly, ry, held, bx, by, vx, vy} = g
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

def Pong.draw(+d: Nat, code: Nat, +x0: U32, +y0: U32, +g: Pong) -> Image:
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
          tl tr bl br = Pong.draw(e, Pong.code(e, x0, y0, g), x0, y0, g)
            Pong.draw(e, Pong.code(e, x1, y0, g), x1, y0, g)
            Pong.draw(e, Pong.code(e, x0, y1, g), x0, y1, g)
            Pong.draw(e, Pong.code(e, x1, y1, g), x1, y1, g)
          Qua{tl, tr, bl, br}

def Pong.view(g: Pong) -> Image:
  +g2 = g
  Pong.draw(9n, Pong.code(9n, 0, 0, g2), 0, 0, g2)

def main() -> IO(Unit):
  App.run(~Pong, ~(Pong.view, Pong.tick), "Pong", 512, 512, Pong.init())
