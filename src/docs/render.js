"use strict";
// Bend explainer.
// Rules: a screen is EITHER one sentence OR one picture, never both.
// One new thing per beat, held long enough to read it out loud twice.
// In a sentence, *stars* mark the words that carry the idea, +plus+ is
// green, _under_ is red, a line that starts with ~ is a dim aside, a line
// that starts with # is a title, and an empty line is a breath of space.
// Twin lines are written to the same length, so a slide reads as one block.
//
// PACING BASELINE, measured on a real reader: a new word costs 0.32s to read;
// a number costs double, because it is read digit by digit. A sentence beat
// computes its own length AND when each of its lines appears -- a line lands
// only once the line above it has been read -- then holds one breath plus
// 25% of the whole reading time, the look-back over the finished slide. A
// picture beat is given the seconds its motion needs plus a HOLD of >= 2.5s.
// A slide marked "punch" is a punchline: it holds 30% longer. A slide marked
// "quick" is a section title: it holds one breath and no look-back.

const READ = 0.32;
const cost = s => (s = s.replace(/[*+_~#%/]/g, "").trim()) ? s.split(/\s+/)
                   .reduce((n, w) => n + (/\d/.test(w) ? 2 : 1), 0) : 0;

const co = "co", punch = "punch", quick = "quick", TAG = new Set([co, punch, quick]);
const BEATS = [
  ["say", "What is the *ideal programming language*", "for those who *stopped reading code*?"],
  ["say", "*1. It must be FAST*", "~large codebases must *compile quickly*", "~CPUs & GPUs must exec at *peak speeds*",
          "*2. Vibe-coding must WORK*", "~agents must write *correct code* in it", "~humans must *keep control* of the code",
          "/All else is fluff."],
  ["check"],
  ["bench", "gameoflife"],
  ["say", "And it *parallelizes*!"],
  ["par", "gameoflife"],
  ["say", "Parallelism is *nearly automatic*.", "The whole language *runs on GPUs*."],
  ["say", "#How is that possible?"],
  ["say", "1. The user writes a *parallel call*."],
  ["example", "call"],
  ["say", "2. The runtime *spreads the workload*."],
  ["dist"],
  ["say", "3. Each core computes a *partial result*."],
  ["eval"],
  ["say", "4. An aggregator produces the *final result*."],
  ["reduce"],
  ["say", "This is not limited to *simple functions*.", "",
          "The *entire language* compiles to kernels.", "",
          "Objects, arrays, allocation, collection,", "pattern matching, closures and recursion.", "",
          "*Every feature runs natively on the GPU.*"],
  ["say", "How about *vibe-coding*?"],
  ["say", "In Bend,", "you can *stop models*", "from *making mistakes*", "by demanding *proofs*."],
  ["say", "#Here's how it works."],
  ["say", "Consider a game with one law:", "*the player cannot win*"],
  ["intro"],
  ["say", "So far, it works!"],
  ["say", "Now, suppose we use this prompt:", "%\"let the player *wrap around*\""],
  ["say", "#What happens next?"],
  ["say", "#In other languages:"],
  ["walk"],
  ["say", "Nothing prevents AIs from breaking the law."],
  ["say", "#In Bend:"],
  ["block"],
  ["say", "The AI placed a wall!", "The law is preserved."],
  ["say", "#But why?"],
  ["say", "Because of:", "#laws.bend"],
  ["laws"],
  ["say", "Bend makes it *mathematically impossible*", "to write any code that breaks *laws.bend*."],
  ["say", "%*PROMPT:* \"Create a teleport skill!\"", "*MODEL:* It will not pass through walls."],
  ["say", "%*PROMPT:* \"Make it pass through walls!\"", "*MODEL:* The room is now surrounded by steel."],
  ["say", "%*PROMPT:* \"Make it pass through *anything*!\"", "*MODEL:* The room now kills you."],
  ["say", "No matter how *crazy* your prompt is,", "the AI is *unable* to break the laws.", "",
          "It must find a *harmless workaround*,", "so it can write the *demanded proof*."],
  ["say", "In short,", "*laws.bend* is *AGENTS.md*", "except *backed by proof*."],
  ["say", "With *laws.bend*,", "%\"make no mistakes\"", "becomes +enforceable+.", punch],
  ["say", "So, that's Bend:", "a language that is *fast*", "where *vibe-coding works*", "and not much else."],
  ["end"],
];

const W = 1280, H = 720;
const BG = "#ffffff", INK = "#151a20", DIM = "#6c7681", FAINT = "#aeb6bf";
const CARD = "#f6f8fa", EDGE = "#e2e7ec", GREEN = "#0f8a45", RED = "#cf2230";
const BLUE = "#1a4f8a", SKY = "#dbe7f5", MIST = "#eef2f6", AMBER = "#d98c00", GRAY = "#c4ccd5";
const MONO = "Menlo,ui-monospace,monospace";

let cx = null;
function setCtx(c) { cx = c; }

// ------------------------------------------------------------------ helpers
const clamp = (x, a, b) => x < a ? a : x > b ? b : x;
const ease  = x => { x = clamp(x, 0, 1); return x*x*(3 - 2*x); };
const lerp  = (a, b, x) => a + (b - a)*x;
const num   = x => Math.round(x).toString().replace(/\B(?=(\d{3})+(?!\d))/g, ",");
const rnd   = i => { const s = Math.sin(i*12.9898)*43758.5453; return s - Math.floor(s); };

function font(size, bold) { cx.font = (bold ? "bold " : "") + size + "px " + MONO; }
function T(s, x, y, size, color, align, bold) {
  font(size, bold); cx.fillStyle = color; cx.textAlign = align || "left";
  cx.fillText(s, x, y); cx.textAlign = "left";
}
// centred sentence with emphasis: *bold*  +green+  _red_
function rich(s, x, y, size, color) {
  const toks = [];
  for (let i = 0; i < s.length; ) {
    const c = s[i], j = "*+_".includes(c) ? s.indexOf(c, i + 1) : -1;
    if (j > i) { toks.push([s.slice(i + 1, j), c]); i = j + 1; continue; }
    let e = i + 1; while (e < s.length && !"*+_".includes(s[e])) e++;
    toks.push([s.slice(i, e), ""]); i = e;
  }
  let total = 0;
  toks.forEach(([p, m]) => { font(size, !!m); total += cx.measureText(p).width; });
  let px = x - total/2;
  toks.forEach(([p, m]) => {
    font(size, !!m);
    cx.fillStyle = m === "+" ? GREEN : m === "_" ? RED : m === "*" ? INK : (color || INK);
    cx.fillText(p, px, y); px += cx.measureText(p).width;
  });
}
function box(x, y, w, h, r, fill, stroke, lw) {
  cx.beginPath(); cx.roundRect(x, y, Math.max(w, 0.5), Math.max(h, 0.5), r);
  if (fill) { cx.fillStyle = fill; cx.fill(); }
  if (stroke) { cx.strokeStyle = stroke; cx.lineWidth = lw || 1; cx.stroke(); cx.lineWidth = 1; }
}
// a bowed arrow: a curve from (x0,y0) to (x1,y1) that bulges k of its
// length to the side (k < 0: the other side), drawn up to fraction a of it.
// With via, the curve bends through that control point instead, so the
// head points the way via -> tip runs.
function bow(x0, y0, x1, y1, k, color, a, via) {
  const A = a === undefined ? 1 : clamp(a, 0, 1);
  if (A <= 0) return;
  const dx = x1 - x0, dy = y1 - y0;
  const [mx, my] = via || [(x0 + x1)/2 - k*dy, (y0 + y1)/2 + k*dx];
  const n = 24, P = [];
  for (let i = 0; i <= n; i++) {
    const t = A*i/n, s = 1 - t;
    P.push([s*s*x0 + 2*s*t*mx + t*t*x1, s*s*y0 + 2*s*t*my + t*t*y1]);
  }
  cx.strokeStyle = color; cx.lineWidth = 2.5; cx.lineCap = "round"; cx.lineJoin = "round";
  cx.beginPath(); P.forEach(([x, y], i) => i ? cx.lineTo(x, y) : cx.moveTo(x, y)); cx.stroke();
  const [ex, ey] = P[n], [px, py] = P[n - 1], l = Math.hypot(ex - px, ey - py) || 1;
  const ux = (ex - px)/l, uy = (ey - py)/l;
  cx.beginPath();
  cx.moveTo(ex - 13*ux + 7*uy, ey - 13*uy - 7*ux); cx.lineTo(ex, ey);
  cx.lineTo(ex - 13*ux - 7*uy, ey - 13*uy + 7*ux);
  cx.stroke(); cx.lineWidth = 1;
}
// a word that swaps at time t0: the old one is gone before the new one comes
const outA = (u, t0) => 1 - ease((u - t0)/0.25);
const inA  = (u, t0) => ease((u - t0 - 0.3)/0.3);

// ------------------------------------------------------------------ code
const KW = new Set(["def", "type", "is", "Data", "match", "case", "import", "as",
                    "forall", "assert", "do", "return"]);
function codeLine(s, x, y, size) {
  font(size);
  const re = /("[^"]*"|#.*$|[A-Za-z_][A-Za-z0-9_.]*|\d+n?|\s+|.)/g;
  let m, px = x;
  while ((m = re.exec(s)) !== null) {
    const t = m[0], kw = KW.has(t);
    font(size, kw);
    cx.fillStyle = t[0] === "#" ? DIM : t[0] === "\"" ? GREEN : kw ? BLUE : INK;
    cx.fillText(t, px, y); px += cx.measureText(t).width;
  }
  font(size);
}
// a file card: a white page with the lines
function codeCard(lines, x, y, w, size, pitch) {
  box(x, y, w, lines.length*pitch + 44, 10, "#ffffff", EDGE, 1.5);
  lines.forEach((l, i) => codeLine(l, x + 28, y + 36 + i*pitch, size));
}

const SUM_SRC = `def sum(+d: Nat, +i: U32) -> U32:
  match d:
    case 0n:
      i
    case 1n+p:
      a b = sum(p, i * 2) sum(p, i * 2 + 1)
      a + b`.split("\n");

// laws.bend, for the reader: the namespaces and the equality's braces are
// left out (that sugar comes later)
const LAWS_SRC = `# LAW: no sequence of moves results
# in the player winning the game.
assert winning_is_a_bug:
  forall moves: List<Move>
  board = init()
  board = apply(board, moves)
  is_won(board) == False`.split("\n");

// ------------------------------------------------------------------ benches
// Every number is a pin from bench/runtime/_pin_apple_m4_max_.txt and
// bench/checker/_pin_apple_m4_max_.txt (2026-08-31, commit 64fc4b7): the
// same Bend binary on one core, on all 16 cores, and on the GPU, against
// its native twins in C, TypeScript and Lean.
const BENCH = {
  gameoflife: { title: "game of life", rivals: [["TypeScript", 18.778], ["Lean", 13.922], ["C", 6.821]],
                seq: 5.458, par: 0.475, gpu: 0.082 },
};
const CHECK = [["Isabelle", 300, true], ["Agda", 300, true], ["Lean", 18.356],
               ["Rocq", 5.951], ["Bend", 0.344]];

const secs = s => (s >= 10 ? s.toFixed(1) : s.toFixed(2)) + "s";
const times = x => (x >= 10 ? Math.round(x) : x.toFixed(1)) + "x";

const BASE = 545, BARH = 330, BW = 110;
const slotX = (i, n, gap) => W/2 - (n*BW + (n - 1)*gap)/2 + i*(BW + gap);
const barTop = (v, vmax) => BASE - BARH*v/vmax;
// one bar: rises from the baseline, its value above, its name below
function bar(x, v, vmax, name, color, a, over, mul) {
  const m = mul === undefined ? 1 : mul;
  if (a <= 0 || m <= 0) return;
  const h = BARH*v/vmax*ease(a);
  cx.globalAlpha = m;
  if (over) {
    box(x, BASE - h, BW, h, 4, "#eef1f4");
    cx.save(); cx.beginPath(); cx.rect(x, BASE - h, BW, h); cx.clip();
    cx.strokeStyle = GRAY; cx.lineWidth = 2; cx.beginPath();
    for (let d = -h; d < BW; d += 12) { cx.moveTo(x + d, BASE); cx.lineTo(x + d + h, BASE - h); }
    cx.stroke(); cx.restore(); cx.lineWidth = 1;
  } else box(x, BASE - h, BW, h, 4, color);
  cx.globalAlpha = m*ease((a - 0.5)/0.5);
  T(over ? ">5 min" : secs(v), x + BW/2, BASE - h - 14, 22, INK, "center", true);
  T(name, x + BW/2, BASE + 32, 20, color === BLUE ? BLUE : DIM, "center", color === BLUE);
  cx.globalAlpha = 1;
}
// one readout above the parallel bars; its arrow bows out to the
// 16-thread bar at TP, then swings over to the GPU bar at TG
const TP = 3.5, TG = 7.7;
const G3 = 100, SPX = slotX(1, 3, G3) + BW + G3/2, SPY = 280;
function speedup(B, u) {
  const a = ease((u - TP)/0.6), sw = ease((u - TG)/0.7);
  if (a <= 0) return;
  const dy = 14*(1 - a);
  const xp = slotX(1, 3, G3) + BW/2, xg = slotX(2, 3, G3) + BW/2;
  const yp = barTop(B.par, B.seq) - 44, yg = barTop(B.gpu, B.seq) - 44;
  const readout = (x, n, chip, al) => {
    cx.globalAlpha = a*al;
    T(times(B.seq/x) + " faster", SPX, SPY + dy, 24, BLUE, "center", true);
    rich("with " + n + " *" + chip + "* threads", SPX, SPY + 30 + dy, 20, DIM);
  };
  readout(B.par, "16", "CPU", outA(u, TG));
  readout(B.gpu, "16384", "GPU", inA(u, TG));
  cx.globalAlpha = a;
  const tx = lerp(xp, xg, sw), ty = lerp(yp, yg, sw);
  bow(SPX, SPY + 48 + dy, tx, ty, -0.28*clamp((tx - SPX)/60, -1, 1), BLUE, a);
  cx.globalAlpha = 1;
}
const S = {};

// the chart: the three rivals and Bend, rising one at a time if rise; as
// go climbs the rivals fade, Bend slides to the left slot and the axis
// zooms onto it. Returns the axis.
function chart(B, u, go, rise) {
  const all = B.rivals.concat([["Bend", B.seq]]);
  const vmax = Math.max(...all.map(r => r[1])), vz = lerp(vmax, B.seq, go);
  rich("Bend runs *FAST*", W/2, 96, 30);
  all.forEach(([name, v], i) => {
    const a = rise ? ease((u - 1.0 - i*1.3)/0.5) : 1;
    if (i < 3) bar(slotX(i, 4, 70), v, vmax, name, GRAY, a, false, 1 - go);
    else bar(lerp(slotX(3, 4, 70), slotX(0, 3, G3), go), v, vz, "Bend", BLUE, a);
  });
  cx.globalAlpha = rise ? ease((u - 6.4)/0.5) : 1;
  T(B.title + " · Apple M4 Max", W/2, 640, 20, DIM, "center");
  cx.globalAlpha = 1;
  return vz;
}
// four bars, one at a time, then the machine, then Bend's bar pointed out
S.bench = (u, dur, b) => {
  const B = BENCH[b[2]], vmax = Math.max(...B.rivals.map(r => r[1]), B.seq);
  chart(B, u, 0, true);
  const pa = ease((u - 7.4)/0.5);
  cx.globalAlpha = pa;
  T("matches C (single-core)", 930, 266, 26, AMBER, "center", true);
  bow(940, 290, slotX(3, 4, 70) + BW/2, barTop(B.seq, vmax) - 42, -0.2, AMBER, pa);
  cx.globalAlpha = 1;
};
// the same chart: the rivals leave, then the 16-thread bar rises, then the
// GPU's, one readout pointing at each in turn
S.par = (u, dur, b) => {
  const B = BENCH[b[2]], vz = chart(B, u, ease((u - 0.8)/0.9), false);
  bar(slotX(1, 3, G3), B.par, vz, "Bend", BLUE, ease((u - 2.6)/0.5));
  bar(slotX(2, 3, G3), B.gpu, vz, "Bend", BLUE, ease((u - 6.8)/0.5));
  speedup(B, u);
};

// five bars, then the gap between Bend and the field, pointed out
S.check = (u, dur) => {
  const vmax = 2*18.356;
  rich("Bend compiles *FAST*", W/2, 96, 30);
  CHECK.forEach(([name, v, over], i) =>
    bar(slotX(i, 5, 70), over ? vmax : v, vmax, name, name === "Bend" ? BLUE : GRAY,
        ease((u - 1.0 - i*1.3)/0.5), over));
  cx.globalAlpha = ease((u - 7.8)/0.5);
  T("3,200 generic instantiations · Apple M4 Max", W/2, 640, 20, DIM, "center");
  const pa = ease((u - 9.2)/0.5);
  cx.globalAlpha = pa;
  T("up to 100x faster", 930, 330, 26, AMBER, "center", true);
  T("than other checkers", 930, 362, 26, AMBER, "center", true);
  bow(950, 385, slotX(4, 5, 70) + BW/2, BASE - 42, -0.25, AMBER, pa);
  cx.globalAlpha = 1;
};

// ------------------------------------------------------------------ game
// The board is drawn from the same level main.bend prints: '#' walls, the
// flag at (1,1), the player at (9,6). Two levels: the room sealed by two
// walls and the map's edge (base), and the shipped one, with two more walls
// on the far edges (far). Pastel tiles on the white page, a title above.
const GW = 14, GH = 10, TILE = 46, BX = W/2 - GW*TILE/2, BY = 126;
const PAL = { floor: ["#f5f7fa", "#e9eef4"], wall: "#b9c6da", cap: "#d3dce9", hit: "#f3c6b2", hitcap: "#f9dccf",
              pole: "#b39b70", cloth: "#f6c66d", skin: "#8fcfe9", eye: "#2f3b4c", gold: "#d9a441",
              pill: "#fde9e6", rim: "#f0aaa1", pillInk: "#a3302a" };
function wallsOf(v) {
  const s = new Set(), add = (x, y) => s.add(x + "," + y);
  for (let y = 0; y <= 3; y++) add(4, y);
  for (let x = 0; x <= 4; x++) add(x, 3);
  if (v === "far") {
    for (let x = 0; x <= 4; x++) add(x, 9);
    for (let y = 0; y <= 3; y++) add(13, y);
  }
  return s;
}
function spaced(s, x, y, size, color, gap) {
  font(size, true); cx.fillStyle = color;
  let w = 0; for (const c of s) w += cx.measureText(c).width + gap;
  let px = x - (w - gap)/2;
  for (const c of s) { cx.fillText(c, px, y); px += cx.measureText(c).width + gap; }
}
const tile = (x, y, fill) => box(BX + x*TILE + 1.5, BY + y*TILE + 1.5, TILE - 3, TILE - 3, 7, fill);
function drawFlag(px, py) {
  const k = TILE/40;
  cx.strokeStyle = PAL.pole; cx.lineWidth = 2.5; cx.lineCap = "round"; cx.beginPath();
  cx.moveTo(px + 14*k, py + 31*k); cx.lineTo(px + 14*k, py + 9*k); cx.stroke(); cx.lineWidth = 1;
  cx.fillStyle = PAL.cloth; cx.beginPath();
  cx.moveTo(px + 15*k, py + 9*k); cx.lineTo(px + 31*k, py + 14.5*k); cx.lineTo(px + 15*k, py + 20*k);
  cx.closePath(); cx.fill();
}
function player(px, py) {
  const k = TILE/40;
  cx.save(); cx.translate(px + TILE/2, py + TILE/2);
  cx.fillStyle = PAL.skin; cx.beginPath(); cx.arc(0, 0, 12.5*k, 0, Math.PI*2); cx.fill();
  cx.fillStyle = PAL.eye; cx.beginPath();
  cx.arc(-4.5*k, -2*k, 2.2*k, 0, Math.PI*2); cx.arc(4.5*k, -2*k, 2.2*k, 0, Math.PI*2); cx.fill();
  cx.restore();
}
// the screenshot: the title and the board. flag says whether the flag is
// still there, pill is the alpha of the banner, hit a wall tile lit by a bump
function gameCard(v, px, py, flag, pill, hit) {
  const walls = wallsOf(v);
  spaced("WINNING IS A BUG", W/2, 96, 22, PAL.gold, 6);
  for (let y = 0; y < GH; y++) for (let x = 0; x < GW; x++) {
    if (!walls.has(x + "," + y)) { tile(x, y, PAL.floor[(x + y) % 2]); continue; }
    const lit = hit && hit[0] === x && hit[1] === y;
    tile(x, y, lit ? PAL.hit : PAL.wall);
    box(BX + x*TILE + 7, BY + y*TILE + 7, TILE - 14, 12, 3, lit ? PAL.hitcap : PAL.cap);
  }
  cx.save(); cx.beginPath(); cx.rect(BX, BY, GW*TILE, GH*TILE); cx.clip();
  if (flag) drawFlag(BX + TILE, BY + TILE);
  player(BX + px*TILE, BY + py*TILE);
  cx.restore();
  if (pill > 0) {
    const py0 = BY + GH*TILE/2 - 48;
    cx.globalAlpha = pill;
    box(W/2 - 170, py0, 340, 96, 14, PAL.pill, PAL.rim, 1.5);
    T("PLAYER WON", W/2, py0 + 41, 24, PAL.pillInk, "center", true);
    T("LAW BROKEN", W/2, py0 + 76, 24, PAL.pillInk, "center", true);
    cx.globalAlpha = 1;
  }
}
// a line under the board
function footer(s, a, color) {
  if (a <= 0) return;
  cx.globalAlpha = a; T(s, W/2, 664, 26, color || INK, "center", true); cx.globalAlpha = 1;
}
// A route is a list of cells; every step takes STEP, so the player moves at
// one speed. A jump of more than one cell is a teleport (off one edge, on
// at the other) and takes no time.
const STEP = 0.4;
const routeDur = r => r.reduce((t, c, i) => i && Math.abs(c[0] - r[i - 1][0]) + Math.abs(c[1] - r[i - 1][1]) <= 1 ? t + STEP : t, 0);
function routeAt(r, u) {
  let t = 0;
  for (let i = 0; i + 1 < r.length; i++) {
    const [ax, ay] = r[i], [bx, by] = r[i + 1];
    if (Math.abs(bx - ax) + Math.abs(by - ay) > 1) continue;
    if (u < t + STEP) { const f = (u - t)/STEP; return [lerp(ax, bx, f), lerp(ay, by, f)]; }
    t += STEP;
  }
  return r[r.length - 1];
}
const up = (x, y0, y1) => { const p = []; for (let y = y0; y >= y1; y--) p.push([x, y]); return p; };
// walk a route from t0, then slam three times into the wall past its end
const BUMP = 0.7, BUMPS = 3;
function walkBump(r, dir, wall, u, t0) {
  const v = u - t0, tw = routeDur(r);
  if (v < tw) return routeAt(r, Math.max(v, 0)).concat([null]);
  const [ex, ey] = r[r.length - 1], tb = (v - tw)/BUMP, g = tb - Math.floor(tb);
  if (tb >= BUMPS) return [ex, ey, null];
  const d = g < 0.25 ? g/0.25 : g < 0.5 ? (0.5 - g)/0.25 : 0;
  return [ex + 0.3*d*dir, ey, g > 0.2 && g < 0.4 ? wall : null];
}

// the game, introduced: the player and the goal pointed out, the law under
// the board, then the player walks up to the room and slams into its wall
const I0 = 6.0;
const INTRO = up(9, 6, 1).concat([[8, 1], [7, 1], [6, 1], [5, 1]]);
S.intro = (u, dur) => {
  const [x, y, hit] = walkBump(INTRO, -1, [4, 1], u, I0);
  gameCard("base", x, y, true, 0, hit);
  const gone = 1 - ease((u - I0 + 0.6)/0.4);
  cx.globalAlpha = ease((u - 1.0)/0.4)*gone;
  T("player", 1130, BY + 6.5*TILE + 8, 26, AMBER, "center", true);
  bow(1072, BY + 6.5*TILE, BX + 10*TILE + 6, BY + 6.5*TILE, 0.15, AMBER);
  cx.globalAlpha = ease((u - 1.9)/0.4)*gone;
  T("goal", 150, BY + 1.5*TILE + 8, 26, AMBER, "center", true);
  bow(205, BY + 1.5*TILE, BX + TILE - 6, BY + 1.5*TILE, -0.15, AMBER);
  cx.globalAlpha = 1;
  footer("law: player can't catch the flag", ease((u - 3.2)/0.4), RED);
};

// other languages: the player goes up to the flag's row, right off the
// edge, in on the left, and takes the flag: the wrap dropped it in the room
const T0W = 1.8;
const WIN = up(9, 6, 1).concat([[10, 1], [11, 1], [12, 1], [13, 1], [14, 1], [-1, 1], [0, 1], [1, 1]]);
S.walk = (u, dur) => {
  const [x, y] = routeAt(WIN, Math.max(u - T0W, 0)), done = T0W + routeDur(WIN);
  gameCard("base", x, y, u < done, ease((u - done - 0.7)/0.4), null);
};

// Bend: the same walk on the shipped level meets a wall on the edge, and
// the player slams into it
const BLOCK = up(9, 6, 1).concat([[10, 1], [11, 1], [12, 1]]);
S.block = (u, dur) => {
  const [x, y, hit] = walkBump(BLOCK, 1, [13, 1], u, 1.2);
  gameCard("far", x, y, true, 0, hit);
};

// ------------------------------------------------------------------ code beats
// what laws.bend is, then the file itself, held long enough to read twice
S.laws = (u, dur) => {
  rich("*laws.bend* is a list of *invariants*", W/2, 140, 30);
  cx.globalAlpha = ease((u - 2.0)/0.4); rich("that models are *forced* to respect.", W/2, 190, 30);
  cx.globalAlpha = ease((u - 3.8)/0.4); rich("Below is the *winning-is-a-bug* law:", W/2, 270, 30);
  cx.globalAlpha = ease((u - 5.6)/0.5); codeCard(LAWS_SRC, W/2 - 300, 325, 600, 20, 34);
  cx.globalAlpha = 1;
};


// an example program: its page, a note with arrows into the lines that
// carry the idea, and the idea's name under it
const EX = {
  call: { src: SUM_SRC, size: 20, pitch: 32, y: 170, at: 2.0, gap: 1.4, dur: 8.0,
          notes: [{ s: "parallel call", side: "B", hits: [[5, "sum(", 0], [5, "sum(", 1]] }] },
};
S.example = (u, dur, b) => {
  const E = EX[b[2]], w = 800, x = W/2 - w/2, y = E.y, h = E.src.length*E.pitch + 44;
  codeCard(E.src, x, y, w, E.size, E.pitch);
  font(E.size); const cw = cx.measureText("M").width;
  const spanX = ([ln, needle, nth, tail]) => {
    let c = -1; for (let k = 0; k <= nth; k++) c = E.src[ln].indexOf(needle, c + 1);
    return x + 28 + (tail ? c + needle.length : c)*cw;
  };
  const lineY = ln => y + 36 + ln*E.pitch;
  E.notes.forEach((n, i) => {
    const a = ease((u - E.at - i*E.gap)/0.4);
    if (a <= 0) return;
    cx.globalAlpha = a;
    font(26, true); const tw = cx.measureText(n.s).width;
    if (n.side === "B") {
      const cy = y + h + 50;
      T(n.s, W/2, cy, 26, AMBER, "center", true);
      // each arrow leaves the label sideways and arrives from straight
      // below, so its head points up at the word
      n.hits.forEach((hit, j) => {
        const side = n.hits.length > 1 ? (j ? 1 : -1) : 0, tx = spanX(hit) + 2*cw;
        bow(W/2 + side*(tw/2 - 10), cy - 30, tx, lineY(hit[0]) + 10, 0, AMBER, 1, [tx, cy - 30]);
      });
    } else {
      const L = n.side === "L", lx = L ? 120 : W - 120;
      const ly = n.hits.reduce((t, hit) => t + lineY(hit[0]), 0)/n.hits.length;
      T(n.s, lx, ly + 2, 26, AMBER, "center", true);
      n.hits.forEach(hit =>
        bow(lx + (L ? 1 : -1)*(tw/2 + 12), ly - 6, spanX(hit) + (hit[3] ? 8 : -8), lineY(hit[0]) - 6, L ? -0.12 : 0.12, AMBER));
    }
    cx.globalAlpha = 1;
  });
};
// ------------------------------------------------------------------ the cube
// The GPU is a static 128 x 128 grid of threads: the cube. sum(24) splits in
// two, then four, ... until one task sits on every thread; each thread works
// its task down to a number; then the numbers flow toward the top-left
// corner, half the grid at a time, until one cell holds the result.
//
// One camera serves all three beats. Grid coordinates put (0,0) at the
// grid's top-left corner and CS is one cell; at scale 1 with the camera on
// the grid's centre, the grid is a 500px square in the middle of the screen.
const N = 128, LEVELS = 14, GS = 500, CS = GS/N, GCEN = GS/2;
const dims = k => [1 << Math.ceil(k/2), 1 << Math.floor(k/2)];
function cam(cpx, cpy, s) {
  return { cpx, cpy, s, at: (gx, gy) => [W/2 + s*(gx - cpx), H/2 + s*(gy - cpy)] };
}
const camLerp = (a, b, p) =>
  cam(lerp(a.cpx, b.cpx, p), lerp(a.cpy, b.cpy, p), Math.exp(lerp(Math.log(a.s), Math.log(b.s), p)));
const CAM0 = cam(GCEN, GCEN, 1);
const ZOOM = 92;                               // one cell fills 360px
const CAM1 = cam(CS/2, CS/2, ZOOM);             // the top-left thread, where the result lands
const MID = 64, CAME = cam((MID + 0.5)*CS, (MID + 0.5)*CS, ZOOM);   // the thread the dive lands on
// a block of the grid, cw x ch cells with its top-left at (c, r), as a rect
function blockRect(camr, c, r, cw, ch) {
  const [x, y] = camr.at(c*CS, r*CS);
  return [x, y, cw*CS*camr.s, ch*CS*camr.s];
}
const offscreen = (x, y, w, h) => x + w < 0 || x > W || y + h < 0 || y > H;
// text in a cell is one fixed fraction of the cell, whatever it says; it
// is skipped once it would be under 5px
const fitText = (w, h) => Math.min(w, h)*0.17;
// the gap between cells never drops under 1.2px, so the lattice reads at
// any zoom; tiny cells deepen their fill by the share the gap takes, so a
// block keeps its colour on average as the camera moves
const RGB = {};
const rgb = h => RGB[h] || (RGB[h] = [1, 3, 5].map(i => parseInt(h.slice(i, i + 2), 16)));
const deepen = (h, k) => "rgb(" + rgb(h).map(v => Math.max(0, Math.round(255 - (255 - v)*k))).join(",") + ")";
function cellBox(x, y, w, h, fill, a) {
  if (a !== undefined) cx.globalAlpha = a;
  const g = clamp(Math.min(w, h)*0.12, 1.2, 8), c = Math.max((w - g)/w*(h - g)/h, 0.3);
  cx.fillStyle = deepen(fill, Math.min(1/c, 1.5)); cx.fillRect(x + g/2, y + g/2, w - g, h - g);
  if (a !== undefined) cx.globalAlpha = 1;
}
// Numbers wear 2048's tiles (gabrielecirulli/2048, style/main.css): the 2
// and 4 tiles' beige while the values are small, the 8..64 climb from orange
// to red over the levels where the numbers can be read, and the 2048 yellow
// for the total alone. Text is 2048's: dark on beige, near-white from 8 up.
const TILES = ["#eee4da", "#ede0c8", "#f2b179", "#f59563", "#f67c5f", "#f65e3b", "#edc22e"];
const mix = (h1, h2, f) => "#" + rgb(h1).map((c, k) => Math.round(lerp(c, rgb(h2)[k], f)).toString(16).padStart(2, "0")).join("");
// a value's rung on the tiles, fractional: its reduce level (log2 of value / leaf) mapped
// so levels 0..6 span the beiges, 6..13 the orange-to-red, 13..14 the yellow
function rung(v) {
  const l = clamp(Math.log2(v/LEAF), 0, LEVELS);
  return l < 6 ? l/6 : l < 13 ? 2 + (l - 6)*3/7 : 5 + (l - 13);
}
function heat(v) {
  const t = rung(v), i = Math.min(Math.floor(t), TILES.length - 2);
  return mix(TILES[i], TILES[i + 1], t - i);
}
const ink = v => rung(v) < 1.5 ? "#776e65" : "#f9f6f2";
function cellText(s, x, y, w, h, a, color) {
  const fs = fitText(w, h);
  if (fs < 5 || a <= 0) return;
  cx.globalAlpha = a;
  T(s, x + w/2, y + h/2 + fs*0.36, fs, color || BLUE, "center", true);
  cx.globalAlpha = 1;
}
// a label to the right of a picture, its arrow bowing in to the edge
function pointer(s, x1, y1, a) {
  if (a <= 0) return;
  cx.globalAlpha = a;
  T(s, 1075, 300, 26, AMBER, "center", true);
  bow(1020, 322, x1, y1, -0.3, AMBER, a);
  cx.globalAlpha = 1;
}

// Step 1. Level k is a cols x rows grid of slots. Between levels each label
// splits: it fades where it stands while two children ride from its centre
// out to their own slots. The boxes come in as the grid gets dense, so the
// first splits are text alone and the last ones are the cube taking shape.
const boxA = k => clamp((k - 2)/9, 0, 1);
const splitDur = k => 1.9*Math.pow(0.82, k);
const cutDur = d => Math.min(0.6, d*0.7);
const lab = k => "sum(" + (24 - k) + ")";
function slotBoxes(k, a) {
  if (a <= 0) return;
  const [cols, rows] = dims(k), w = GS/cols, h = GS/rows;
  for (let r = 0; r < rows; r++) for (let c = 0; c < cols; c++) {
    const [x, y] = CAM0.at(c*w, r*h);
    cellBox(x, y, w, h, SKY, a);
  }
}
// labels of level k, each moved from its parent's centre by m (0 = at the
// parent, 1 = home), at alpha a
function slotLabels(k, m, a) {
  if (a <= 0) return;
  const [cols, rows] = dims(k), w = GS/cols, h = GS/rows;
  const [pc, pr] = k ? dims(k - 1) : [1, 1], pw = GS/pc, ph = GS/pr;
  for (let r = 0; r < rows; r++) for (let c = 0; c < cols; c++) {
    const hx = (c + 0.5)*w, hy = (r + 0.5)*h;
    const px = (Math.floor(c*pc/cols) + 0.5)*pw, py = (Math.floor(r*pr/rows) + 0.5)*ph;
    const [x, y] = CAM0.at(lerp(px, hx, m) - w/2, lerp(py, hy, m) - h/2);
    cellText(lab(k), x, y, w, h, a);
  }
}
S.dist = (u, dur) => {
  let k = 0, t = 1.2;
  while (k < LEVELS && u >= t + splitDur(k)) { t += splitDur(k); k++; }
  const d = splitDur(k), p = k < LEVELS ? ease((u - (t + d - cutDur(d)))/cutDur(d)) : 0;
  slotBoxes(k, boxA(k));
  slotLabels(k, 1, 1 - clamp(p/0.4, 0, 1));
  if (p > 0) {
    slotBoxes(k + 1, boxA(k + 1)*p);
    slotLabels(k + 1, ease(p), clamp((p - 0.3)/0.5, 0, 1));
  }
  const [cols, rows] = dims(p > 0.5 ? k + 1 : k), n = cols*rows;
  T(n === 1 ? "1 task" : num(n) + " tasks", W/2, 660, 24, INK, "center");
  pointer("That's your GPU!", W/2 + GS/2 + 8, 392, ease((u - (dur - 3.4))/0.5));
};

// Step 2. Every thread works its sum(10,0) down one call at a time while the
// camera dives toward one thread: the dive is quick at first, so the text
// turns readable early, hundreds of threads mid-work, then slows onto one
// thread, which finishes its sum alone on the screen.
const EVAL = ["sum(10,0)", "sum(9,10)", "sum(8,19)", "sum(7,27)", "sum(6,34)", "sum(5,40)",
              "sum(4,45)", "sum(3,49)", "sum(2,52)", "sum(1,54)", "sum(0,55)", "55"];
const EVALV = [0, 10, 19, 27, 34, 40, 45, 49, 52, 54, 55, 55];
const ESTEP = 1.0, E0 = 0.8, DIVE = 6.8, EDONE = E0 + (EVAL.length - 1)*ESTEP;
const phase = (c, r) => c === MID && r === MID ? 0 : rnd(c*7919 + r*104729)*0.9;
S.eval = (u, dur) => {
  const p = clamp((u - E0)/DIVE, 0, 1), z = 1 - (1 - p)*(1 - p), camr = camLerp(CAM0, CAME, z);
  const others = 1 - clamp((p - 0.82)/0.18, 0, 1);
  for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) {
    const [x, y, w, h] = blockRect(camr, c, r, 1, 1);
    if (offscreen(x, y, w, h)) continue;
    const a = c === MID && r === MID ? 1 : others;
    if (a <= 0) continue;
    const j = clamp(Math.floor((u - E0 - phase(c, r))/ESTEP), 0, EVAL.length - 1);
    cellBox(x, y, w, h, j ? heat(EVALV[j]) : SKY, a);
    cellText(EVAL[j], x, y, w, h, a, j ? ink(EVALV[j]) : BLUE);
  }
  // the grid's name rides on the grid and leaves the screen as the camera dives
  const [lx, ly] = camr.at(GCEN, 0);
  cx.globalAlpha = others; T("your GPU", lx, ly - 18, 24, INK, "center", true);
  const [ex, ey] = CAME.at((MID + 1)*CS, (MID + 0.5)*CS);
  pointer("one GPU thread", ex + 6, ey + 12, ease((u - E0 - DIVE - 0.2)/0.5));
  cx.globalAlpha = ease((u - EDONE - 0.3)/0.4);
  T("partial result", W/2, 600, 24, AMBER, "center", true);
  cx.globalAlpha = 1;
};

// Step 3. The camera pulls back to the whole cube, every thread holding its
// 55. Then the numbers flow: the right half of the grid slides onto the left
// half and lands, each cell adding what arrived; then the bottom half onto
// the top; and so on, the live region shrinking toward the top-left corner
// while the camera follows it in, until one cell holds the total.
const R0 = 2.6, LEAF = 55;
const flowDur = j => 0.35 + 1.3*Math.pow(j/13, 2);
const region = j => [N >> Math.ceil(j/2), N >> Math.floor(j/2)];
function camFor(j) {
  if (j >= LEVELS) return CAM1;
  const [w, h] = region(j);
  return cam(w*CS/2, h*CS/2, Math.min(0.84*W/(w*CS), 0.84*H/(h*CS), ZOOM));
}
S.reduce = (u, dur) => {
  let j = 0, t = R0;
  while (j < LEVELS && u >= t + flowDur(j)) { t += flowDur(j); j++; }
  const p = j < LEVELS ? clamp((u - t)/flowDur(j), 0, 1) : 1, m = ease(p);
  const camr = u < R0 ? camLerp(CAME, camFor(0), ease(u/R0)) : camLerp(camFor(j), camFor(j + 1), m);
  const [w, h] = region(j), vert = j % 2 === 0;          // even steps fold the width
  const val = num(LEAF*Math.pow(2, j)), val2 = num(LEAF*Math.pow(2, j + 1));
  const v1 = LEAF*Math.pow(2, j), v2 = LEAF*Math.pow(2, j + 1);
  const fill = heat(v1), fill2 = heat(v2), ink1 = ink(v1), ink2 = ink(v2);
  const landed = clamp((p - 0.82)/0.18, 0, 1);
  // the other threads return as the camera pulls back, and leave again once
  // the total is in: the last frame is one cell alone
  const others = u < R0 ? clamp(u/0.6, 0, 1) : j < LEVELS ? 1 : 1 - ease((u - t - 0.5)/0.6);
  // the static grid: empty cells faint, live cells blue
  for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) {
    const [x, y, cw, ch] = blockRect(camr, c, r, 1, 1);
    if (offscreen(x, y, cw, ch)) continue;
    const live = c < w && r < h, src = live && (vert ? c >= w/2 : r >= h/2);
    const a = u < R0 && !(c === MID && r === MID) ? others : j >= LEVELS && !(c === 0 && r === 0) ? others : 1;
    if (a <= 0) continue;
    if (!live || (src && p > 0)) { cellBox(x, y, cw, ch, MIST, a); continue; }
    cellBox(x, y, cw, ch, j >= LEVELS || u < R0 ? fill : mix(fill, fill2, landed), a);
    if (j >= LEVELS) cellText(val, x, y, cw, ch, 1, ink1);
    else if (u < R0) cellText(val, x, y, cw, ch, a, ink1);
    else {
      cellText(val, x, y, cw, ch, 1 - landed, ink1);
      cellText(val2, x, y, cw, ch, landed, ink2);
    }
  }
  // the moving half: one sheet of cells sliding onto its neighbours
  if (j < LEVELS && p > 0) {
    const dx = vert ? -w/2*m : 0, dy = vert ? 0 : -h/2*m;
    const c0 = vert ? w/2 : 0, r0 = vert ? 0 : h/2, cw = vert ? w/2 : w, chh = vert ? h : h/2;
    for (let r = r0; r < r0 + chh; r++) for (let c = c0; c < c0 + cw; c++) {
      const [x, y, sw, sh] = blockRect(camr, c + dx, r + dy, 1, 1);
      if (offscreen(x, y, sw, sh)) continue;
      cellBox(x, y, sw, sh, fill, 1 - landed);
      cellText(val, x, y, sw, sh, 1 - landed, ink1);
    }
  }
  // the grid's name is written on the grid, as in the dive: it stays put
  // over the grid's top edge while the camera moves
  const [lx, ly] = camr.at(GCEN, 0);
  cx.globalAlpha = others; T("your GPU", lx, ly - 18, 24, INK, "center", true);
  cx.globalAlpha = ease((u - (dur - 3.0))/0.4);
  T("final result!", W/2, 600, 24, GREEN, "center", true);
  cx.globalAlpha = 1;
};

// ------------------------------------------------------------------- beats
// ~ is a dim aside in smaller type, % a full-size line in dim ink, # is a
// title, "" is a breath of space
function sayLines(b) {
  return b.slice(2).filter(s => !TAG.has(s)).map(s => s[0] === "~"
    ? { s: s.slice(1), size: 22, pitch: 40, color: DIM }
    : s[0] === "%" ? { s: s.slice(1), size: 34, pitch: 62, color: DIM }
    : s[0] === "#" ? { s: "*" + s.slice(1) + "*", size: 44, pitch: 78, color: INK }
    : s[0] === "/" ? { s: s.slice(1), size: 30, pitch: 56, color: INK, slant: true }
    : s === "" ? { s, size: 34, pitch: 30, color: INK }
    : { s, size: 34, pitch: 62, color: INK });
}
// a slide too wide or too tall for the screen shrinks as a whole, so its
// lines keep their proportions
S.say = (u, dur, b) => {
  const ls = sayLines(b);
  const gap = (i, k) => k*((ls[i - 1].pitch + ls[i].pitch)/2 + (ls[i - 1].size === 22 && ls[i].size !== 22 ? 18 : 0));
  let k = 1, hgt = 0;
  ls.forEach(l => { font(l.size, true); k = Math.min(k, (W - 120)/cx.measureText(l.s.replace(/[*+_]/g, "")).width); });
  ls.forEach((l, i) => { if (i) hgt += gap(i, 1); });
  k = Math.min(k, (H - 130)/hgt);
  let y = 372 - hgt*k/2 + 12*k;
  ls.forEach((l, i) => {
    if (i) y += gap(i, k);
    cx.globalAlpha = i === 0 ? 1 : ease((u - b.at[i])/0.4);
    if (l.slant) { cx.save(); cx.transform(1, 0, -0.2, 1, 0.2*y, 0); }
    rich(l.s, W/2, y, l.size*k, l.color);
    if (l.slant) cx.restore();
    cx.globalAlpha = 1;
  });
};

S.end = (u, dur) => {
  T("Bend", W/2, 290, 64, INK, "center", true);
  cx.globalAlpha = ease((u - 0.6)/0.5);
  T("fast  ·  vibe-coding works  ·  and nothing else", W/2, 360, 24, GREEN, "center");
  cx.globalAlpha = ease((u - 1.8)/0.5);
  T("Python syntax · C speed · CPU and GPU · proofs", W/2, 430, 19, DIM, "center");
  T("github.com/HigherOrderCO/Bend", W/2, 480, 22, "#1a5fd0", "center");
  cx.globalAlpha = 1;
};

// ------------------------------------------------------------------ pacing
// Sentence beats size themselves: line i lands once line i-1 has been read,
// and the beat ends one breath after the last line. Picture beats get the
// seconds their motion needs plus a hold.
const FIXED = { bench: 11.0, par: 12.5, check: 14.0, intro: 14.5, walk: 10.5, block: 9.0, laws: 17.0,
                dist: 15.5, eval: 15.0, reduce: 19.0, end: 32.0 };
for (const b of BEATS) {
  if (b[0] === "say") {
    const ls = b.slice(1).filter(s => !TAG.has(s));
    let t = 0; b.at = ls.map(s => { const a = t; t += READ*cost(s) + 0.4; return a; });
    const d = b.includes(quick) ? t + 0.3 : (t*1.25 + 0.8)*(b.includes(punch) ? 1.3 : 1);
    b.splice(1, 0, Math.max(2.4, d));
  } else b.splice(1, 0, b[0] === "example" ? EX[b[1]].dur : FIXED[b[0]]);
}
const T0 = []; let DUR = 0;
for (const b of BEATS) { T0.push(DUR); DUR += b[1]; }
const SCENES = BEATS.map(b => [b[0] === "say"
  ? "“" + b[2].replace(/[*+_~#%/]/g, "") : b[0] + (b[2] && b[0] !== "say" ? " " + b[2] : ""), b[1]]);

// -------------------------------------------------------------------- main
function draw(t) {
  cx.fillStyle = BG; cx.fillRect(0, 0, W, H);
  let i = 0;
  while (i < BEATS.length - 1 && t >= T0[i] + BEATS[i][1]) i++;
  const b = BEATS[i], dur = b[1], u = clamp(t - T0[i], 0, dur), nxt = BEATS[i + 1];
  S[b[0]](u, dur, b);
  const inA  = b.includes(co) ? 1 : ease(u/0.3);
  const outA = nxt && nxt.includes(co) ? 1 : ease((dur - u)/0.3);
  const f = 1 - Math.min(inA, outA);
  if (f > 0) { cx.fillStyle = `rgba(255,255,255,${f})`; cx.fillRect(0, 0, W, H); }
}

if (typeof module !== "undefined") module.exports = { draw, setCtx, DUR, SCENES, T0 };
