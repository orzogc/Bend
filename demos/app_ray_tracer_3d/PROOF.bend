# Fly -- the proofs. This file imports the flight (as Ray) and the
# claims (as Laws) and fills every law. The two key-store laws are
# inductions over the held list with a case analysis on the slot (and
# the pad lemmas cover a slot past the end); the same-slot case of
# press_others is refuted (True is not False). esc_quits is an
# induction over the events before the Esc; the Key arm is general
# over the key's quit flag. frames_bound is an induction over the tick
# times: one tick adds at most one frame (clock_le, general over the
# within-the-second flag), and the order lemmas (le_refl, le_trans,
# add_mono, add_succ) chain it with the induction hypothesis. The
# sanity laws compute.
import Base
import ./main.bend as Ray
import ./LAWS.bend as Laws

def disc(e: {True{} == False{} : Bool}) -> Empty:
  %e : Ray.Fly.truth(_)
  Unit{}

# The key store
# -------------

law pad_reads:
  for k: Nat
  for v: Bool
  {Ray.Fly.get(Ray.Fly.pad(k, v), k) == v : Bool}

def pad_reads(k, v):
  match k:
    case 0n:
      {==}
    case 1n+j:
      pad_reads(j, v)

def Laws.press_reads(held, k, v):
  match held:
    case Nil{}:
      pad_reads(k, v)
    case h <> t:
      match k:
        case 0n:
          {==}
        case 1n+j:
          Laws.press_reads(t, j, v)

law pad_others:
  for k: Nat
  for j: Nat
  for v: Bool
  for ne: {Ray.Fly.same(j, k) == False{} : Bool}
  {Ray.Fly.get(Ray.Fly.pad(k, v), j) == False{} : Bool}

def pad_others(k, j, v, ne):
  match k j:
    case 0n 0n:
      Empty.absurd({v == False{} : Bool}, disc(ne))
    case 0n 1n+jp:
      {==}
    case 1n+kp 0n:
      {==}
    case 1n+kp 1n+jp:
      pad_others(kp, jp, v, ne)

def Laws.press_others(held, k, j, v, ne):
  match held:
    case Nil{}:
      pad_others(k, j, v, ne)
    case h <> t:
      match k j:
        case 0n 0n:
          Empty.absurd({v == h : Bool}, disc(ne))
        case 0n 1n+jp:
          {==}
        case 1n+kp 0n:
          {==}
        case 1n+kp 1n+jp:
          Laws.press_others(t, kp, jp, v, ne)

# Esc anywhere
# ------------

law esc_arm:
  for b: Bool
  for s: Ray.Fly
  for -rest: List<Event>
  for ih: @r: Ray.Fly -> {Ray.Fly.events(rest, r) == None{} : Maybe<Ray.Fly>}
  {Maybe.bind(&1, Ray.Fly, Ray.Fly, Ray.Fly.quit(b, s),
      r => Ray.Fly.events(rest, r)) == None{} : Maybe<Ray.Fly>}

def esc_arm(b, s, rest, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      ih(s)

def Laws.esc_quits(pre, post, s):
  match pre:
    case Nil{}:
      match s:
        case Ray.Fly{x, y, z, yaw, pitch, held, t0, frames, fps}:
          {==}
    case Key{+code, +down} <> rest:
      match s:
        case Ray.Fly{x, y, z, yaw, pitch, held, t0, frames, fps}:
          esc_arm(Ray.Fly.esc(code, down),
            Ray.Fly{x, y, z, yaw, pitch, Ray.Fly.press(down, code, held), t0,
              frames, fps},
            Ray.Fly.cat(rest, Key{27, True{}} <> post),
            r => Laws.esc_quits(rest, post, r))
    case Mouse{x, y, button, down} <> rest:
      Laws.esc_quits(rest, post, s)
    case Move{x, y} <> rest:
      Laws.esc_quits(rest, post, s)
    case Close{} <> rest:
      {==}

# The fps counter
# ---------------

law le_refl:
  for n: Nat
  Ray.Fly.truth(Ray.Fly.le(n, n))

def le_refl(n):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      le_refl(p)

law le_trans:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: Ray.Fly.truth(Ray.Fly.le(a, b))
  for bc: Ray.Fly.truth(Ray.Fly.le(b, c))
  Ray.Fly.truth(Ray.Fly.le(a, c))

def le_trans(a, b, c, ab, bc):
  match a:
    case 0n:
      Unit{}
    case 1n+x:
      match b:
        case 0n:
          Empty.absurd(Ray.Fly.truth(Ray.Fly.le(1n+x, c)), ab)
        case 1n+y:
          match c:
            case 0n:
              Empty.absurd(Ray.Fly.truth(Ray.Fly.le(1n+x, 0n)), bc)
            case 1n+z:
              le_trans(x, y, z, ab, bc)

law add_mono:
  for c: Nat
  for -a: Nat
  for -b: Nat
  for h: Ray.Fly.truth(Ray.Fly.le(a, b))
  Ray.Fly.truth(Ray.Fly.le(Nat.add(c, a), Nat.add(c, b)))

def add_mono(c, a, b, h):
  match c:
    case 0n:
      h
    case 1n+p:
      add_mono(p, a, b, h)

law add_succ:
  for a: Nat
  for -b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

def add_succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

law bound_step:
  for +c: Nat
  for -a: Nat
  for -b: Nat
  for h: Ray.Fly.truth(Ray.Fly.le(a, 1n+b))
  Ray.Fly.truth(Ray.Fly.le(Nat.add(c, a), 1n+Nat.add(c, b)))

def bound_step(c, a, b, h):
  %add_succ(c, b) : Ray.Fly.truth(Ray.Fly.le(Nat.add(c, a), _))
  add_mono(c, a, 1n+b, h)

# one tick adds at most one frame, whatever the within-the-second flag
law count_le:
  for w: Bool
  for now: Nat
  for x: F32
  for y: F32
  for z: F32
  for yaw: F32
  for pitch: F32
  for held: List<&2, Bool>
  for t0: Nat
  for frames: Nat
  for fps: Nat
  Ray.Fly.truth(Ray.Fly.le(Ray.Fly.frames_of(Ray.Fly.count(w, now,
    Ray.Fly{x, y, z, yaw, pitch, held, t0, 1n+frames, fps})), 1n+frames))

def count_le(w, now, x, y, z, yaw, pitch, held, t0, frames, fps):
  match w:
    case True{}:
      le_refl(1n+frames)
    case False{}:
      Unit{}

law clock_le:
  for +t: Nat
  for s: Ray.Fly
  Ray.Fly.truth(Ray.Fly.le(Ray.Fly.frames_of(Ray.Fly.clock(t, s)),
    1n+Ray.Fly.frames_of(s)))

def clock_le(t, s):
  match s:
    case Ray.Fly{x, y, z, yaw, pitch, held, +t0, frames, fps}:
      count_le(Nat.is_lt(Nat.sub(t, t0), 1000n), t, x, y, z, yaw, pitch, held,
        t0, frames, fps)

def Laws.frames_bound(ts, s):
  match ts:
    case Nil{}:
      le_refl(Ray.Fly.frames_of(s))
    case t <> rest:
      le_trans(Ray.Fly.frames_of(Ray.Fly.clocks(rest, Ray.Fly.clock(t, s))),
        Nat.add(Ray.Fly.len(rest), Ray.Fly.frames_of(Ray.Fly.clock(t, s))),
        1n+Nat.add(Ray.Fly.len(rest), Ray.Fly.frames_of(s)),
        Laws.frames_bound(rest, Ray.Fly.clock(t, s)),
        bound_step(Ray.Fly.len(rest), Ray.Fly.frames_of(Ray.Fly.clock(t, s)),
          Ray.Fly.frames_of(s), clock_le(t, s)))

# Sanity
# ------

def Laws.slots():
  ({==}, {==}, {==})

def Laws.fps_digits():
  ({==}, {==}, {==}, {==}, {==}, {==})
