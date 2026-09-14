# Pong -- the laws. Claims about the game's pure logic: Esc quits, the
# paddles stay in the field, the ball keeps or flips its speed, the ball
# is always drawn orange, and the first frame moves the ball by its
# speed. PROOF.bend must prove every one.
import Base
import ./main.bend as Game

# LAW: Esc pressed quits: Pong.key on code 27 down gives None for any
# game state, and so does the close button.
law quits:
  for +g: Game.Pong
  {Game.Pong.key(27, True{}, g) == None{} : Maybe<Game.Pong>}
  & {Game.Pong.event(Close{}, g) == None{} : Maybe<Game.Pong>}

# LAW: the paddles stay in the field: a wrapped (negative) position
# clamps to 0 for any y; the left paddle at the top (0) with W held
# stays at 0; at the bottom (416, the last row where its 96 pixels fit)
# with S held it stays at 416; with no key held it stays at 208.
law paddle_field:
  for +y: U32
  {Game.Pong.clamp(True{}, y) == 0 : U32}
  & {Game.Pong.paddle(0, 1, 0n, 1n) == 0 : U32}
  & {Game.Pong.paddle(416, 2, 0n, 1n) == 416 : U32}
  & {Game.Pong.paddle(208, 0, 0n, 1n) == 208 : U32}

# LAW: the ball keeps its speed off a miss and flips it on a hit: for
# any v, bounce(False{}, v) is v; bounce(True{}, 3) is the wrap of -3,
# and a second hit restores 3.
law bounce:
  for +v: U32
  {Game.Pong.bounce(False{}, v) == v : U32}
  & {Game.Pong.bounce(True{}, 3) == 4294967293 : U32}
  & {Game.Pong.bounce(True{}, Game.Pong.bounce(True{}, 3)) == 3 : U32}

# LAW: the ball is always drawn orange: a cell that touches the ball is
# coded 1n, whatever the paddle tests say, and code 1n paints 16763904.
law ball_orange:
  for pad: Bool
  for none: Bool
  {Game.Pong.color(Game.Pong.code_of(True{}, pad, none)) == 16763904 : U32}

# LAW: the first frame: one step from the start moves the ball by its
# speed (3, 3), leaves both paddles at 208 and keeps the speeds.
law first_step:
  {Game.Pong.step(Game.Pong.init())
    == Game.Pong{208, 208, 0, 255, 255, 3, 3} : Game.Pong}
