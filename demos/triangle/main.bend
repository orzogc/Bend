# Triangle: the hello triangle over base's App and Window kit. One orange
# triangle on a teal field; a click inside it adds a white square to the
# tally along the top edge; Esc or the close button quits. The state is
# the click count. A frame is an Image quadtree: kind classifies each
# cell against the tally strip and the triangle (a cell is inside when
# its four corners are, outside when they all lie beyond one edge) and
# draw emits one Pix the moment the cell is uniform, so a frame costs a
# few thousand nodes along the edges. The caller classifies the child, so
# the recursion is one def descending on the depth.
#
#   bend demos/triangle/main.bend -o triangle && ./triangle
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

def Tri.view(n: U32) -> U32 & Image:
  +m = n
  (m, Tri.draw(9n, Tri.kind(9n, 0, 0, m), 0, 0, m))

def Tri.quit(esc: Bool, n: U32) -> Maybe<U32>:
  match esc:
    case True{}:
      None{}
    case False{}:
      Some{n}

def Tri.event(e: Event, +n: U32) -> Maybe<U32>:
  match e:
    case Key{code, down}:
      Tri.quit(Bool.and(down, U32.is_eq(code, 27)), n)
    case Mouse{x, y, button, down}:
      Some{Tri.pick(Bool.and(down, Tri.inside(x, y)), (n + 1 : U32), n)}
    case Move{x, y}:
      Some{n}
    case Close{}:
      None{}

def Tri.events(events: List<Event>, n: U32) -> Maybe<U32>:
  match events:
    case Nil{}:
      Some{n}
    case Con{e, rest}:
      Maybe.bind(&1, U32, U32, Tri.event(e, n), m => Tri.events(rest, m))

def Tri.tick(events: List<Event>, n: U32) -> IO(Maybe<U32>):
  IO.pure(Maybe<U32>, Tri.events(events, n))

def main() -> IO(Unit):
  App.run(~U32, ~App{Tri.view, Tri.tick}, "Triangle", 512, 512, 0)
