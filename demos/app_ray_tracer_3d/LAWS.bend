# Fly -- the laws. Claims about the flight's pure control logic over
# any state: the held keys are a store that a key event writes at one
# slot (pressing a key sets that key; it changes no other key), an Esc
# anywhere in a frame's events quits, and the fps counter never counts
# more frames than there were ticks. The F32 scene is not claimed.
# PROOF.bend must prove every one.
import Base
import ./main.bend as Ray

# LAW: after a key is pressed (or released), that key reads pressed (or
# released), for any slot and any held keys.
law press_reads:
  for held: List<&2, Bool>
  for k: Nat
  for v: Bool
  {Ray.Fly.get(Ray.Fly.set(held, k, v), k) == v : Bool}

# LAW: pressing or releasing one key changes no other key: for any two
# different slots j and k, slot j reads the same before and after.
law press_others:
  for held: List<&2, Bool>
  for k: Nat
  for j: Nat
  for v: Bool
  for ne: {Ray.Fly.same(j, k) == False{} : Bool}
  {Ray.Fly.get(Ray.Fly.set(held, k, v), j) == Ray.Fly.get(held, j) : Bool}

# LAW: an Esc key-down anywhere in a frame's events quits, whatever the
# events before and after it and whatever the state.
law esc_quits:
  for pre: List<Event>
  for post: List<Event>
  for s: Ray.Fly
  {Ray.Fly.events(Ray.Fly.cat(pre, Key{27, True{}} <> post), s) == None{}
    : Maybe<Ray.Fly>}

# LAW: the fps counter never counts more frames than there were ticks:
# after any list of tick times, the frames of the current second are at
# most their number plus the frames before.
law frames_bound:
  for +ts: List<&2, Nat>
  for +s: Ray.Fly
  Ray.Fly.truth(Ray.Fly.le(Ray.Fly.frames_of(Ray.Fly.clocks(ts, s)),
    Nat.add(Ray.Fly.len(ts), Ray.Fly.frames_of(s))))

# LAW: the key slots: W is 0, Down is 9, Esc has no slot the flight
# reads (sanity).
law slots:
  {Ray.Fly.slot(119) == 0n : Nat}
  & {Ray.Fly.slot(63233) == 9n : Nat}
  & {Ray.Fly.slot(27) == 10n : Nat}

# LAW: the fps digits: a count under 10 blanks its two leading digits
# and shows its units; 123 shows 1, 2, 3 (sanity).
law fps_digits:
  {Ray.Fly.digit(0n, 7) == 10 : U32}
  & {Ray.Fly.digit(1n, 7) == 10 : U32}
  & {Ray.Fly.digit(2n, 7) == 7 : U32}
  & {Ray.Fly.digit(0n, 123) == 1 : U32}
  & {Ray.Fly.digit(1n, 123) == 2 : U32}
  & {Ray.Fly.digit(2n, 123) == 3 : U32}
