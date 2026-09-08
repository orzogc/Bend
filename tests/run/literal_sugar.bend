# interp-only: literal sugar round-trips in the printer -- strings as
# "..", nats as Nn, chars as '.'
# ported from bend3: the def-per-block form becomes one tuple main
# (bend4's CLI prints main only); the list block returns with the list
# literal (elements Nat, whose print is compact) and the tuple prints
# as Tuple{..} (bend4's printer does not re-sugar tuples)
import Base

law main:
  (String & Nat & (U32 & U32) & Char & List<&2, Nat>)

def main():
  (String.append("hi", "\n"), Nat.add(1n, 2n), (3, 4), 'a', [5n, 6n])

#|Tuple{"hi\n", Tuple{3n, Tuple{Tuple{U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, Tuple{'a', Con{5n, Con{6n, Nil{}}}}}}}
