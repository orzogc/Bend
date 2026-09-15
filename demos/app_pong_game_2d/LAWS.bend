# Pong -- the laws. Claims about the game's whole step over any state:
# a frame never moves a paddle or the ball out of the field, an Esc
# anywhere in a frame's events quits, the start is in the field, the
# first frame moves the ball by its speed, and a key pressed then
# released is off again. PROOF.bend must prove every one.
import Base
import ./main.bend as Game

# LAW: the field invariant: from any state whose paddles are within
# 0..416 and whose ball is within 0..504 on both axes, one step (any
# held keys, any ball direction, any wall or paddle bounce, any reset)
# gives a state within the same bounds.
law step_in_field:
  for +g: Game.Pong
  for h: Game.Pong.in_field(g)
  Game.Pong.in_field(Game.Pong.step(g))

# LAW: an Esc key-down anywhere in a frame's events quits, whatever the
# events before and after it and whatever the state.
law esc_quits:
  for pre: List<Event>
  for post: List<Event>
  for g: Game.Pong
  {Game.Pong.events(Game.Pong.cat(pre, Key{27, True{}} <> post), g) == None{}
    : Maybe<Game.Pong>}

# LAW: the start is in the field (sanity).
law init_in_field:
  Game.Pong.in_field(Game.Pong.init())

# LAW: the first frame: one step from the start moves the ball by its
# speed (3, 3) and leaves both paddles at 208 (sanity).
law first_step:
  {Game.Pong.step(Game.Pong.init())
    == Game.Pong{208n, 208n, Game.Keys{False{}, False{}, False{}, False{}},
      255n, 255n, True{}, True{}} : Game.Pong}

# LAW: W pressed then released is off, and the other keys keep their
# state, whatever they were (sanity).
law keys_lens:
  for w: Bool
  for s: Bool
  for up: Bool
  for down: Bool
  {Game.Pong.press(False{}, 119, Game.Pong.press(True{}, 119,
      Game.Keys{w, s, up, down}))
    == Game.Keys{False{}, s, up, down} : Game.Pong.Keys}
