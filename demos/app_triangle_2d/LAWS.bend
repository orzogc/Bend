# Triangle -- the laws. Claims about the tally's whole behaviour over
# any frame: replaying any event list from any count gives exactly the
# count plus the clicks inside, unless an event quits; an Esc anywhere
# in the list quits; an event that is neither a click inside nor a quit
# keeps the count. PROOF.bend must prove every one.
import Base
import ./main.bend as App

# LAW: replaying any event list from any count: the frame quits (None)
# when some event is Esc down or Close, and otherwise ends at the start
# count plus the number of mouse-downs inside the triangle.
law replay:
  for evs: List<Event>
  for +n: Nat
  {App.Tri.events(evs, n)
    == App.Tri.quit(App.Tri.quits(evs), Nat.add(n, App.Tri.hits(evs)))
    : Maybe<Nat>}

# LAW: an Esc key-down anywhere in a frame's events quits, whatever the
# events before and after it and whatever the count.
law esc_quits:
  for pre: List<Event>
  for post: List<Event>
  for n: Nat
  {App.Tri.events(App.Tri.cat(pre, Key{27, True{}} <> post), n) == None{}
    : Maybe<Nat>}

# LAW: an event that is not a click inside the triangle and not a quit
# (a release, a move, a click outside, any other key) keeps the count.
law keeps:
  for e: Event
  for n: Nat
  for h: {App.Tri.hit(e) == False{} : Bool}
  for q: {App.Tri.quit_of(e) == False{} : Bool}
  {App.Tri.event(e, n) == Some{n} : Maybe<Nat>}

# LAW: a click at the centroid counts, for any count (sanity).
law click_inside:
  for n: Nat
  {App.Tri.event(Mouse{256, 320, 0, True{}}, n) == Some{1n+n} : Maybe<Nat>}
