# Triangle -- the laws. Claims about the program's pure logic: a click
# inside the triangle adds one to the tally, a click outside or a
# release keeps it, Esc and the close button quit, and a cell's code
# follows the geometry. PROOF.bend must prove every one.
import Base
import ./main.bend as App

# LAW: a click inside the triangle adds one to the tally: a mouse-down
# at the centroid (256, 320) gives n + 1 for any count n.
law click_inside:
  for +n: U32
  {App.Tri.event(Mouse{256, 320, 0, True{}}, n) == Some{(n + 1 : U32)}
    : Maybe<U32>}

# LAW: a click outside the triangle keeps the tally, and so does a
# button release anywhere: a mouse event at the corner (0, 0) with any
# down flag, and a mouse-up at any point, give n for any n.
law click_outside:
  for +n: U32
  for d: Bool
  for +x: U32
  for +y: U32
  {App.Tri.event(Mouse{0, 0, 0, d}, n) == Some{n} : Maybe<U32>}
  & {App.Tri.event(Mouse{x, y, 0, False{}}, n) == Some{n} : Maybe<U32>}

# LAW: Esc pressed quits, and so does the close button, for any tally.
law quits:
  for +n: U32
  {App.Tri.event(Key{27, True{}}, n) == None{} : Maybe<U32>}
  & {App.Tri.event(Close{}, n) == None{} : Maybe<U32>}

# LAW: off the tally strip the cell code follows the geometry: a cell
# whose four corners are inside is 1n (orange), a cell beyond one edge
# is 0n (teal), and a cell that is neither splits (3n), whatever the
# strip's size and parity tests say.
law code_off_strip:
  for small: Bool
  for lit: Bool
  for away: Bool
  {App.Tri.code(False{}, small, lit, True{}, away) == 1n : Nat}
  & {App.Tri.code(False{}, small, lit, False{}, True{}) == 0n : Nat}
  & {App.Tri.code(False{}, small, lit, False{}, False{}) == 3n : Nat}
