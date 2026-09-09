# The laws. The human states them; PROOF.bend must prove them.

import Base
import ./main.bend as Game

# LAW: for any sequence of moves, replaying them
# from the start can never lead to victory.
law you_cant_win:
  for moves: List<Game.Move>
  board = Game.replay(Game.start(), moves)
  {Game.is_won(board) == False{} : Bool}

# A board that looks won: the player on the flag's cell, `won` still false.
def looks_won(g: Game.Game) -> Bool:
  Game.Game{x, y, won} = g
  Game.on_flag(x, y) && Bool.not(won)

# LAW: standing on the flag is a win: no sequence of moves leaves the
# player on the flag's cell with `won` false.
law on_flag_wins:
  for moves: List<Game.Move>
  board = Game.replay(Game.start(), moves)
  {looks_won(board) == False{} : Bool}
