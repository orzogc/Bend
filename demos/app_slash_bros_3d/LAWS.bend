# Slash Bros 3D -- the laws. Claims about the sim's pure logic, the
# part the interpreter can evaluate without F32 arithmetic: the tick
# countdown, the key bits, the pause toggle and the route back to the
# title. PROOF.bend proves them.

import Base
import ./main.bend as Slash

# LAW: a countdown never underflows: at 0 it stays 0, and a hit's
# flash (7) falls to 6.
law dec_floor:
  {(Slash.Sim.dec(0), Slash.Sim.dec(7)) == (0, 6) : U32 & U32}

# LAW: w a s d are the bits 1 2 4 8 of the held word, and the arrow
# keys (up 63232, left 63234, down 63233, right 63235) are the same
# four bits.
law arrows_are_wasd:
  {(Slash.Key.mask(119), Slash.Key.mask(97), Slash.Key.mask(115), Slash.Key.mask(100),
    Slash.Key.mask(63232), Slash.Key.mask(63234), Slash.Key.mask(63233), Slash.Key.mask(63235))
   == (1, 2, 4, 8, 1, 2, 4, 8) : U32 & U32 & U32 & U32 & U32 & U32 & U32 & U32}

# LAW: the pause toggles: P during a fight pauses it, P again resumes
# it, and P on the title does nothing.
law pause_toggles:
  {(Slash.Game.paused(Slash.Game.pause(Slash.Game.fresh(0, 1))),
    Slash.Game.paused(Slash.Game.pause(Slash.Game.pause(Slash.Game.fresh(0, 1)))),
    Slash.Game.paused(Slash.Game.pause(Slash.Game.init())))
   == (True{}, False{}, False{}) : Bool & Bool & Bool}

# LAW: K past the fight goes back to the title whatever else is
# tapped: the route on back = True is the initial game, for every
# other flag and every game.
law back_to_title:
  for fresh: Bool
  for pause: Bool
  for live: Bool
  for frozen: Bool
  for +g: Slash.Game
  {Slash.Game.route(True{}, fresh, pause, live, frozen, g) == Slash.Game.init() : Slash.Game}
