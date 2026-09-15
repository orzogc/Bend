# Triangle: the hello triangle over base's App and Window kit. One orange
# triangle on a teal field; a click inside it adds a white square to the
# tally along the top edge; Esc or the close button quits. The state is
# the click count, a Nat (the drawing reads it as a U32 at the edge, so
# LAWS.bend can speak about any count). A frame is an Image quadtree:
# kind classifies each cell against the tally strip and the triangle (a
# cell is inside when its four corners are, outside when they all lie
# beyond one edge) and draw emits one Pix the moment the cell is
# uniform, so a frame costs a few thousand nodes along the edges. The
# caller classifies the child, so the recursion is one def descending on
# the depth. The Spec section names what the laws say: a hit (a click
# inside), a quit (Esc down or Close), and their counts over a list.
#
#   bend demos/app_triangle_2d/main.bend -o hello_triangle && ./hello_triangle
import Base

def Tri.pick(c: Bool, a: U32, b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

def Tri.side(+ax: U32, +ay: U32, +bx: U32, +by: U32, +px: U32, +py: U32)
  -> Bool:
  ((bx - ax) * (py - ay) - (by - ay) * (px - ax) > 2147483647 : U32)

def Tri.inside(+x: U32, +y: U32) -> Bool:
  (Tri.side(256, 64, 64, 448, x, y) && Tri.side(64, 448, 448, 448, x, y)
    && Tri.side(448, 448, 256, 64, x, y))

def Tri.out(
  +ax: U32, +ay: U32, +bx: U32, +by: U32, +x0: U32, +y0: U32, +x1: U32,
  +y1: U32
) -> Bool:
  Bool.not((Tri.side(ax, ay, bx, by, x0, y0) || Tri.side(ax, ay, bx, by, x1, y0)
    || Tri.side(ax, ay, bx, by, x0, y1) || Tri.side(ax, ay, bx, by, x1, y1)))

def Tri.code(strip: Bool, small: Bool, lit: Bool, full: Bool, away: Bool)
  -> Nat:
  match strip, small, lit, full, away:
    case True{}, True{}, True{}, _, _:
      2n
    case True{}, True{}, False{}, _, _:
      0n
    case True{}, False{}, _, _, _:
      3n
    case False{}, _, _, True{}, _:
      1n
    case False{}, _, _, False{}, True{}:
      0n
    case False{}, _, _, False{}, False{}:
      3n

def Tri.kind(d: Nat, +x0: U32, +y0: U32, +n: U32) -> Nat:
  +s = U32.shln(1, d)
  +x1 = (x0 + s : U32)
  +y1 = (y0 + s : U32)
  Tri.code(((y0 < 8) && (x0 < 16 * n) : U32), (s <= 8 : U32),
    U32.is_eq((x0 .&. 8 : U32), 0),
    (Tri.inside(x0, y0) && Tri.inside(x1, y0) && Tri.inside(x0, y1)
      && Tri.inside(x1, y1)),
    (Tri.out(256, 64, 64, 448, x0, y0, x1, y1)
      || Tri.out(64, 448, 448, 448, x0, y0, x1, y1)
      || Tri.out(448, 448, 256, 64, x0, y0, x1, y1)))

def Tri.draw(+d: Nat, kind: Nat, +x0: U32, +y0: U32, +n: U32) -> Image:
  match d:
    case 0n:
      Pix{Tri.pick(Tri.inside(x0, y0), 16744499, 3362125)}
    case 1n+e:
      match kind:
        case 0n:
          Pix{3362125}
        case 1n:
          Pix{16744499}
        case 2n:
          Pix{16777215}
        case _:
          +h = U32.shln(1, e)
          +x1 = (x0 + h : U32)
          +y1 = (y0 + h : U32)
          tl tr bl br = Tri.draw(e, Tri.kind(e, x0, y0, n), x0, y0, n)
            Tri.draw(e, Tri.kind(e, x1, y0, n), x1, y0, n)
            Tri.draw(e, Tri.kind(e, x0, y1, n), x0, y1, n)
            Tri.draw(e, Tri.kind(e, x1, y1, n), x1, y1, n)
          Qua{tl, tr, bl, br}

def Tri.view(n: Nat) -> Nat & Image:
  +m = n
  +u = U32.from_nat(m)
  (m, Tri.draw(9n, Tri.kind(9n, 0, 0, u), 0, 0, u))

def Tri.quit(esc: Bool, n: Nat) -> Maybe<Nat>:
  match esc:
    case True{}:
      None{}
    case False{}:
      Some{n}

def Tri.esc(+code: U32, down: Bool) -> Bool:
  Bool.and(down, U32.is_eq(code, 27))

def Tri.bump(hit: Bool, n: Nat) -> Nat:
  match hit:
    case True{}:
      1n+n
    case False{}:
      n

def Tri.event(e: Event, n: Nat) -> Maybe<Nat>:
  match e:
    case Key{code, down}:
      Tri.quit(Tri.esc(code, down), n)
    case Mouse{x, y, button, down}:
      Some{Tri.bump(Bool.and(down, Tri.inside(x, y)), n)}
    case Move{x, y}:
      Some{n}
    case Close{}:
      None{}

def Tri.events(events: List<Event>, n: Nat) -> Maybe<Nat>:
  match events:
    case Nil{}:
      Some{n}
    case e <> rest:
      Maybe.bind(&1, Nat, Nat, Tri.event(e, n), m => Tri.events(rest, m))

def Tri.tick(events: List<Event>, n: Nat) -> IO(Maybe<Nat>):
  IO.pure(Maybe<Nat>, Tri.events(events, n))

# Spec
# ----
# What LAWS.bend says about the tally: a hit is a mouse-down inside the
# triangle, a quit is Esc down or the close button; hits and quits fold
# them over a frame's event list, and cat joins two lists.

def Tri.hit(e: Event) -> Bool:
  match e:
    case Mouse{x, y, button, down}:
      Bool.and(down, Tri.inside(x, y))
    case _:
      False{}

def Tri.quit_of(e: Event) -> Bool:
  match e:
    case Key{code, down}:
      Tri.esc(code, down)
    case Close{}:
      True{}
    case _:
      False{}

def Tri.hits(events: List<Event>) -> Nat:
  match events:
    case Nil{}:
      0n
    case e <> rest:
      Tri.bump(Tri.hit(e), Tri.hits(rest))

def Tri.quits(events: List<Event>) -> Bool:
  match events:
    case Nil{}:
      False{}
    case e <> rest:
      Bool.or(Tri.quit_of(e), Tri.quits(rest))

def Tri.cat(xs: List<Event>, ys: List<Event>) -> List<Event>:
  match xs:
    case Nil{}:
      ys
    case x <> rest:
      x <> Tri.cat(rest, ys)

def main() -> IO(Unit):
  App.run(~Nat, ~App{Tri.view, Tri.tick}, "Triangle", 512, 512, 0n)
