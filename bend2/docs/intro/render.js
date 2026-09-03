"use strict";
// Bend explainer.
// Rules: a screen is EITHER one sentence OR one picture, never both.
// One new thing per beat, held long enough to read it out loud twice.
// In a sentence, *stars* mark the words that carry the idea, +plus+ is
// green, /slash/ leans, a line that starts with ~ is a dim
// aside, a line that starts with # is a title, and an empty line is a
// breath of space.
// Twin lines are written to the same length, so a slide reads as one block.
//
// PACING BASELINE, measured on a real reader: a new word costs 0.32s to read;
// a number costs double, because it is read digit by digit. A sentence beat
// computes its own length AND when each of its lines appears -- a line lands
// only once the line above it has been read -- then holds one breath plus
// 25% of the whole reading time, the look-back over the finished slide. A
// picture beat is given the seconds its motion needs plus a HOLD of >= 2.5s.
// A slide marked "punch" is a punchline: it holds 30% longer. A slide marked
// "quick" is a section title: it holds one breath and no look-back. A slide
// marked "red" or "green" is written in that ink.

const READ = 0.32;
const cost = s => (s = s.replace(/[*+~#%/]/g, "").trim()) ? s.split(/\s+/)
                   .reduce((n, w) => n + (/\d/.test(w) ? 2 : 1), 0) : 0;

const co = "co", punch = "punch", quick = "quick", left = "left", red = "red", green = "green";
const TAG = new Set([co, punch, quick, left, red, green]);
const BEATS = [
  ["say", "#Bend is a new language", "- that's *FAST* like C", "- that *SCALES* like CUDA",
          "- that *PROVES* like Lean", "- where vibe-coding *WORKS*", left],
  ["check"],
  ["bench", "gameoflife"],
  ["par", "gameoflife", co],
  ["say", "#Parallelism is near-automatic."],
  ["dist"],
  ["eval", co],
  ["reduce", co],
  ["say", "*The entire language can run on GPUs.*", "",
          "Objects, arrays, allocator, collector,", "pattern-matching, closures, recursion.", "",
          "*Everything* compiles to *kernels*!"],
  ["say", "Bend is fast in a single CPU core.", "And scales to massive GPU clusters."],
  ["say", "How about *vibe-coding*?"],
  ["say", "In Bend,", "you can *stop models*", "from *making mistakes*", "by demanding *proofs*."],
  ["say", "#How?"],
  ["reveal", "laws|.|bend", 64],
  ["laws"],
  ["say", "*laws.bend* is *AGENTS.md*", "except backed by *proof*."],
  ["say", "#Example"],
  ["say", "Consider a game with one law:", "%\"the player can't win\""],
  ["intro"],
  ["say", "So far, it works!"],
  ["say", "Now, let's *prompt* a new feature:", "%\"let the map wrap around\""],
  ["say", "Without *laws.bend*:"],
  ["walk"],
  ["say", "Oops! The player won.", "The new feature *broke the law*.", red],
  ["say", "With *laws.bend*:"],
  ["block"],
  ["say", "The AI placed a /wall/!", "Feature landed, *law preserved*.", green],
  ["say", "The rules in *laws.bend* are enforced with the same",
          "algorithm used in proof assistants such as Lean.", "",
          "It is *mathematically impossible* for AI agents to",
          "break its laws. Edits demand correctness proofs.", "",
          "Models either *make no mistakes*, or *fail loudly*."],
  ["say", "And that's Bend:", "a language *fast* like C", "that *scales* like CUDA",
          "that *proves* like Lean", "where vibe-coding *works*."],
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
// centred sentence with emphasis: *bold*  +green+  /oblique/
// (Menlo has no italic, so an oblique run is the text leaned by a skew)
function rich(s, x, y, size, color) {
  const toks = [];
  for (let i = 0; i < s.length; ) {
    const c = s[i], j = "*+/".includes(c) ? s.indexOf(c, i + 1) : -1;
    if (j > i) { toks.push([s.slice(i + 1, j), c]); i = j + 1; continue; }
    let e = i + 1; while (e < s.length && !"*+/".includes(s[e])) e++;
    toks.push([s.slice(i, e), ""]); i = e;
  }
  const bold = m => !!m && m !== "/";
  let total = 0;
  toks.forEach(([p, m]) => { font(size, bold(m)); total += cx.measureText(p).width; });
  let px = x - total/2;
  toks.forEach(([p, m]) => {
    font(size, bold(m));
    cx.fillStyle = m === "+" ? GREEN : (color || INK);
    if (m === "/") { cx.save(); cx.transform(1, 0, -0.2, 1, 0.2*y, 0); }
    cx.fillText(p, px, y); px += cx.measureText(p).width;
    if (m === "/") cx.restore();
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
// ------------------------------------------------------------------ code
const KW = new Set(["def", "type", "is", "Data", "match", "case", "import", "as", "assert", "do", "return"]);
const QUANT = new Set(["forall", "exists"]), CTR = new Set(["True", "False"]);
const COMMENT = "#5a8f4e", PURPLE = "#6f42c1", ORANGE = "#c2410c";
function codeLine(s, x, y, size) {
  font(size);
  const re = /("[^"]*"|#.*$|[A-Za-z_][A-Za-z0-9_.]*|\d+n?|\s+|.)/g;
  let m, px = x;
  while ((m = re.exec(s)) !== null) {
    const t = m[0], kw = KW.has(t) || QUANT.has(t);
    font(size, kw);
    cx.fillStyle = t[0] === "#" ? COMMENT : t[0] === "\"" ? GREEN : KW.has(t) ? BLUE
                 : QUANT.has(t) ? PURPLE : CTR.has(t) ? ORANGE : INK;
    cx.fillText(t, px, y); px += cx.measureText(t).width;
  }
  font(size);
}
// a file card: a gray page with the lines
function codeCard(lines, x, y, w, size, pitch) {
  box(x, y, w, lines.length*pitch + 44, 10, CARD, EDGE, 1.5);
  lines.forEach((l, i) => codeLine(l, x + 28, y + 36 + i*pitch, size));
}

// laws.bend, for the reader: the namespaces and the equality's braces are
// left out (that sugar comes later)
const LAWS_SRC = `# LAW: no move sequence results in victory
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
// one readout straight above a parallel bar: the speedup, the cores it
// took, and an arrow down to the bar
const G3 = 150, SPY = 280;
function speedup(B, v, i, chip, u, t0) {
  const a = ease((u - t0)/0.6);
  if (a <= 0) return;
  const x = slotX(i, 3, G3) + BW/2, dy = 14*(1 - a);
  cx.globalAlpha = a;
  T(times(B.seq/v) + " faster", x, SPY + dy, 24, BLUE, "center", true);
  rich("on *" + chip + "*", x, SPY + 30 + dy, 20, DIM);
  bow(x, SPY + 48 + dy, x, barTop(v, B.seq) - 44, 0, BLUE, a);
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
    const a = rise ? ease((u - 1.0 - i*1.0)/0.5) : 1;
    if (i < 3) bar(slotX(i, 4, 70), v, vmax, name, GRAY, a, false, 1 - go);
    else bar(lerp(slotX(3, 4, 70), slotX(0, 3, G3), go), v, vz, "Bend", BLUE, a);
  });
  cx.globalAlpha = rise ? ease((u - 5.2)/0.5) : 1;
  T(B.title + " · Apple M4 Max", W/2, 640, 20, DIM, "center");
  cx.globalAlpha = 1;
  return vz;
}
// four bars, one at a time, then the machine, then Bend's bar pointed out
S.bench = (u, dur, b) => {
  const B = BENCH[b[2]], vmax = Math.max(...B.rivals.map(r => r[1]), B.seq);
  chart(B, u, 0, true);
  const pa = ease((u - 6.2)/0.5)*(1 - ease((u - dur + 0.6)/0.4));
  cx.globalAlpha = pa;
  T("Competes with C", 930, 250, 26, AMBER, "center", true);
  T("in a single core", 930, 282, 26, AMBER, "center", true);
  bow(940, 305, slotX(3, 4, 70) + BW/2, barTop(B.seq, vmax) - 42, -0.2, AMBER, pa);
  cx.globalAlpha = 1;
};
// the same chart: the rivals leave, then the 16-core bar rises and its
// readout lands, then the GPU's bar and readout; both readouts stay
S.par = (u, dur, b) => {
  const B = BENCH[b[2]], vz = chart(B, u, ease((u - 0.6)/0.9), false);
  bar(slotX(1, 3, G3), B.par, vz, "Bend", BLUE, ease((u - 2.0)/0.5));
  speedup(B, B.par, 1, "16 CPU cores", u, 2.8);
  bar(slotX(2, 3, G3), B.gpu, vz, "Bend", BLUE, ease((u - 5.6)/0.5));
  speedup(B, B.gpu, 2, "16384 GPU cores", u, 6.4);
};

// five bars, then the gap between Bend and the field, pointed out
S.check = (u, dur) => {
  const vmax = 2*18.356;
  rich("Bend compiles *FAST*", W/2, 96, 30);
  CHECK.forEach(([name, v, over], i) =>
    bar(slotX(i, 5, 70), over ? vmax : v, vmax, name, name === "Bend" ? BLUE : GRAY,
        ease((u - 1.0 - i*1.0)/0.5), over));
  cx.globalAlpha = ease((u - 6.2)/0.5);
  T("3,200 generic instantiations · Apple M4 Max", W/2, 640, 20, DIM, "center");
  const pa = ease((u - 7.4)/0.5);
  cx.globalAlpha = pa;
  T("Up to 100x faster", 930, 330, 26, AMBER, "center", true);
  T("than other provers", 930, 362, 26, AMBER, "center", true);
  bow(950, 385, slotX(4, 5, 70) + BW/2, BASE - 42, -0.25, AMBER, pa);
  cx.globalAlpha = 1;
};

// ------------------------------------------------------------------ game
// The board is drawn from the same level main.bend prints: '#' walls, the
// flag at (1,1), the player at (8,5). Two levels: the room sealed by two
// walls and the map's edge (base), and the shipped one, with two more walls
// on the far edges (far). Pastel tiles on the white page, a title above.
const GW = 12, GH = 8, TILE = 56, BX = W/2 - GW*TILE/2, BY = 126;
const PAL = { floor: ["#f5f7fa", "#e9eef4"], wall: "#b9c6da", cap: "#d3dce9", hit: "#f3c6b2", hitcap: "#f9dccf",
              pole: "#b39b70", cloth: "#f6c66d", skin: "#8fcfe9", eye: "#2f3b4c", gold: "#d9a441",
              win: "#fde9e6", winRim: "#f0aaa1", winInk: "#a3302a" };
function wallsOf(v) {
  const s = new Set(), add = (x, y) => s.add(x + "," + y);
  for (let y = 0; y <= 3; y++) add(3, y);
  for (let x = 0; x <= 3; x++) add(x, 3);
  if (v === "far") {
    for (let x = 0; x <= 3; x++) add(x, 7);
    for (let y = 0; y <= 3; y++) add(11, y);
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
// still there, hit a wall tile lit by a bump
function gameCard(v, px, py, flag, hit) {
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
}
// a line under the board
const LAW = "LAW: player can't win.";
function footer(s, a, color) {
  if (a <= 0) return;
  cx.globalAlpha = a; T(s, W/2, 664, 26, color || INK, "center", true); cx.globalAlpha = 1;
}
// A route is a list of cells; every step takes STEP, so the player moves at
// one speed. A jump of more than one cell is a teleport (off one edge, on
// at the other) and takes no time.
const STEP = 0.22;
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
const BUMP = 0.4, BUMPS = 3;
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
const I0 = 3.0;
const INTRO = up(8, 5, 1).concat([[7, 1], [6, 1], [5, 1], [4, 1]]);
S.intro = (u, dur) => {
  const [x, y, hit] = walkBump(INTRO, -1, [3, 1], u, I0);
  gameCard("base", x, y, true, hit);
  const gone = 1 - ease((u - I0 + 0.6)/0.4);
  cx.globalAlpha = ease((u - 0.6)/0.4)*gone;
  T("Player", 1130, BY + 5.5*TILE + 8, 26, AMBER, "center", true);
  bow(1072, BY + 5.5*TILE, BX + 9*TILE + 6, BY + 5.5*TILE, 0.15, AMBER);
  cx.globalAlpha = ease((u - 1.3)/0.4)*gone;
  T("Goal", 150, BY + 1.5*TILE + 8, 26, AMBER, "center", true);
  bow(205, BY + 1.5*TILE, BX + TILE - 6, BY + 1.5*TILE, -0.15, AMBER);
  cx.globalAlpha = 1;
  footer(LAW, ease((u - 2.0)/0.4), GREEN);
};

// laws.bend off: the player goes up to the flag's row, right off the
// edge, in on the left, and takes the flag: the wrap dropped it in the
// room. Victory pops on the board once the flag is gone, and the law
// under the board turns red.
const T0W = 0.6;
const WIN = up(8, 5, 1).concat([[9, 1], [10, 1], [11, 1], [12, 1], [-1, 1], [0, 1], [1, 1]]);
S.walk = (u, dur) => {
  const [x, y] = routeAt(WIN, Math.max(u - T0W, 0)), done = T0W + routeDur(WIN);
  gameCard("base", x, y, u < done, null);
  const pa = ease((u - done - 0.3)/0.4);
  footer(LAW, 1, pa > 0 ? RED : GREEN);
  if (pa > 0) {
    const py = BY + GH*TILE/2 - 40;
    cx.globalAlpha = pa;
    box(W/2 - 150, py, 300, 80, 14, PAL.win, PAL.winRim, 1.5);
    T("YOU WON >:(", W/2, py + 51, 30, PAL.winInk, "center", true);
    cx.globalAlpha = 1;
  }
};

// laws.bend on: the same walk on the shipped level meets a wall on the
// edge, and the player slams into it
const BLOCK = up(8, 5, 1).concat([[9, 1], [10, 1]]);
S.block = (u, dur) => {
  const [x, y, hit] = walkBump(BLOCK, 1, [11, 1], u, T0W);
  gameCard("far", x, y, true, hit);
  footer(LAW, 1, GREEN);
};

// ------------------------------------------------------------------ code beats
// what laws.bend is, then the file under its name, then where the rules go
S.laws = (u, dur) => {
  const x = W/2 - 300, y = 285, h = LAWS_SRC.length*34 + 44;
  rich("A new file that lists *invariants*", W/2, 140, 30);
  cx.globalAlpha = ease((u - 2.0)/0.4); rich("that models are *forced* to follow.", W/2, 190, 30);
  cx.globalAlpha = ease((u - 4.0)/0.5);
  T("laws.bend", x + 28, y - 16, 20, DIM, "left", true);
  codeCard(LAWS_SRC, x, y, 600, 20, 34);
  const pa = ease((u - 7.5)/0.5);
  cx.globalAlpha = pa;
  T("Write your rules here.", W/2, 650, 26, AMBER, "center", true);
  bow(W/2, 618, W/2, y + h + 10, 0, AMBER, pa);
  cx.globalAlpha = 1;
};

// ------------------------------------------------------------------ the cube
// The GPU is a static 128 x 128 grid of cores: the cube. sum(24) splits in
// two, then four, ... until one task sits on every core; each core works
// its task down to a number; then the numbers fold, pairwise and in place,
// the blocks coarsening until one block is the cube and holds the result.
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
// the grid's caption at alpha ac and its pointer at alpha ap: the whole
// grid is seen at scale 1 in the split and the dive, so both sit at fixed
// places
function gridTag(n, ac, ap) {
  if (ac <= 0) return;
  cx.globalAlpha = ac;
  T(n === 1 ? "1 task" : num(n) + " tasks", W/2, 660, 24, INK, "center");
  cx.globalAlpha = 1;
  pointer("GPU", W/2 + GS/2 + 8, 392, ap);
}
const ZOOM = 92;                               // one cell fills 360px
const MID = 64, CAME = cam((MID + 0.5)*CS, (MID + 0.5)*CS, ZOOM);   // the core the dive lands on
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
// Numbers wear 2048's tiles (gabrielecirulli/2048, style/main.css),
// softened a third toward white to sit with the film's pastels, one even
// climb over the whole run: a core's sum goes from the 2 tile's beige to
// the 8 tile's orange as it counts up to 55, then the folds carry the
// totals from that orange to the 64 tile's red, and the final result alone
// wears the 2048 yellow. The ink is 2048's dark brown throughout.
const mix = (h1, h2, f) => "#" + rgb(h1).map((c, k) => Math.round(lerp(c, rgb(h2)[k], f)).toString(16).padStart(2, "0")).join("");
const TILES = ["#eee4da", "#ede0c8", "#f2b179", "#f59563", "#f67c5f", "#f65e3b", "#edc22e"]
              .map(t => mix(t, "#ffffff", 0.35));
const TINK = "#776e65";
// a value's rung on the tiles, fractional: 0..2 while the leaf counts up,
// 2..5 over the fold levels (log2 of value / leaf) but the last, which is 6
function rung(v) {
  const l = clamp(Math.log2(v/LEAF), 0, LEVELS);
  return v <= LEAF ? 2*v/LEAF : l < LEVELS - 1 ? 2 + 3*l/(LEVELS - 1) : 5 + (l - LEVELS + 1);
}
function heat(v) {
  const t = rung(v), i = Math.min(Math.floor(t), TILES.length - 2);
  return mix(TILES[i], TILES[i + 1], t - i);
}
function cellText(s, x, y, w, h, a, color) {
  const fs = fitText(w, h);
  if (fs < 5 || a <= 0) return;
  cx.globalAlpha = a;
  T(s, x + w/2, y + h/2 + fs*0.36, fs, color || BLUE, "center", true);
  cx.globalAlpha = 1;
}
// a label to the right of a picture, its arrow leaving from under the
// label's first letters and bowing in to the edge
function pointer(s, x1, y1, a) {
  if (a <= 0) return;
  cx.globalAlpha = a;
  T(s, 1075, 300, 26, AMBER, "center", true);
  bow(1075 - cx.measureText(s).width/2 + 10, 322, x1, y1, -0.3, AMBER, a);
  cx.globalAlpha = 1;
}

// Step 1. Level k is a cols x rows grid of slots. Between levels each label
// splits: it fades where it stands while two children ride from its centre
// out to their own slots. The boxes come in as the grid gets dense, so the
// first splits are text alone and the last ones are the cube taking shape.
const boxA = k => clamp((k - 2)/9, 0, 1);
const splitDur = k => 0.9*Math.pow(0.8, k);
const D0 = 0.5, DALL = (() => { let t = D0; for (let k = 0; k < LEVELS; k++) t += splitDur(k); return t; })();
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
  let k = 0, t = D0;
  while (k < LEVELS && u >= t + splitDur(k)) { t += splitDur(k); k++; }
  const d = splitDur(k), p = k < LEVELS ? ease((u - (t + d - cutDur(d)))/cutDur(d)) : 0;
  slotBoxes(k, boxA(k));
  slotLabels(k, 1, 1 - clamp(p/0.4, 0, 1));
  if (p > 0) {
    slotBoxes(k + 1, boxA(k + 1)*p);
    slotLabels(k + 1, ease(p), clamp((p - 0.3)/0.5, 0, 1));
  }
  const [cols, rows] = dims(p > 0.5 ? k + 1 : k);
  gridTag(cols*rows, 1, ease((u - DALL - 0.2)/0.4));
};

// Step 2. Every core works its sum(10,0) down one call at a time while the
// camera, after a moment on the whole grid, dives toward one core: the
// dive is quick at first, so the text turns readable early, hundreds of
// cores mid-work, then slows onto one core, which finishes its sum alone
// on the screen.
const EVAL = ["sum(10,0)", "sum(9,10)", "sum(8,19)", "sum(7,27)", "sum(6,34)", "sum(5,40)",
              "sum(4,45)", "sum(3,49)", "sum(2,52)", "sum(1,54)", "sum(0,55)", "55"];
const EVALV = [0, 10, 19, 27, 34, 40, 45, 49, 52, 54, 55, 55];
const ESTEP = 0.5, E0 = 0.5, ED = 0.4, DIVE = 3.5, EDONE = E0 + (EVAL.length - 1)*ESTEP;
const phase = (c, r) => c === MID && r === MID ? 0 : rnd(c*7919 + r*104729)*0.9;
S.eval = (u, dur) => {
  const p = clamp((u - ED)/DIVE, 0, 1), z = 1 - (1 - p)*(1 - p), camr = camLerp(CAM0, CAME, z);
  const others = 1 - clamp((p - 0.82)/0.18, 0, 1);
  for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) {
    const [x, y, w, h] = blockRect(camr, c, r, 1, 1);
    if (offscreen(x, y, w, h)) continue;
    const a = c === MID && r === MID ? 1 : others;
    if (a <= 0) continue;
    const j = clamp(Math.floor((u - E0 - phase(c, r))/ESTEP), 0, EVAL.length - 1);
    cellBox(x, y, w, h, j ? heat(EVALV[j]) : SKY, a);
    cellText(EVAL[j], x, y, w, h, a, j ? TINK : BLUE);
  }
  // the caption and the pointer stay as the dive begins, and fade with it
  const g = 1 - ease((u - ED)/0.4);
  gridTag(N*N, g, g);
  const [ex, ey] = CAME.at((MID + 1)*CS, (MID + 0.5)*CS);
  pointer("GPU core", ex + 6, ey + 12, ease((u - ED - DIVE - 0.2)/0.5));
  cx.globalAlpha = ease((u - EDONE - 0.3)/0.4);
  T("Partial result", W/2, 600, 24, AMBER, "center", true);
  cx.globalAlpha = 1;
};

// Step 3. The camera pulls back to the whole cube, every core holding its
// 55. Then the numbers fold in place, pairwise, the way Bend's runtime
// joins results. A live cell is drawn as the block of cores whose sums it
// holds: 2^ceil(j/2) wide and 2^floor(j/2) tall before step j. Every
// second block slides onto its neighbour in that direction, which pops,
// lit, and swells over both with the doubled sum. So the blocks coarsen,
// step by step, until one block is the whole cube and holds the total. A
// fold takes flowDur: the slide is its first SLIDE, the swell the rest.
const ZO = 1.2, R0 = 1.5, LEAF = 55, SLIDE = 0.65;
const flowDur = j => 0.35 + 0.15*j/(LEVELS - 1);
const RDONE = (() => { let t = R0; for (let j = 0; j < LEVELS; j++) t += flowDur(j); return t; })();
const stride = j => [1 << Math.ceil(j/2), 1 << Math.floor(j/2)];
S.reduce = (u, dur) => {
  let j = 0, t = R0;
  while (j < LEVELS && u >= t + flowDur(j)) { t += flowDur(j); j++; }
  const folding = u >= R0 && j < LEVELS, p = folding ? clamp((u - t)/flowDur(j), 0, 1) : 0;
  const m = ease(p/SLIDE), landed = folding && p >= SLIDE, q = ease((p - SLIDE)/(1 - SLIDE));
  const camr = u < R0 ? camLerp(CAME, CAM0, ease(u/ZO)) : CAM0;
  const [sx, sy] = stride(j), vert = j % 2 === 0;          // even steps fold columns
  const v1 = LEAF*Math.pow(2, j), v2 = 2*v1, val = num(v1), val2 = num(v2);
  const fill = heat(v1), fill2 = heat(v2);
  const pop = 1 + 0.12*Math.sin(Math.PI*q), lit = mix(fill2, "#ffffff", 0.3*Math.sin(Math.PI*q));
  // the other cores return as the camera pulls back
  const others = clamp(u/0.6, 0, 1);
  // the lattice of cores, seen where a block has just slid away
  if (folding) for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) {
    const [x, y, cw, ch] = blockRect(camr, c, r, 1, 1);
    if (!offscreen(x, y, cw, ch)) cellBox(x, y, cw, ch, MIST);
  }
  // the blocks: at rest, a mover riding onto its neighbour (drawn after
  // it, so it passes on top), or a neighbour swelling over the sum
  for (let r = 0; r < N; r += sy) for (let c = 0; c < N; c += sx) {
    const mv = folding && (vert ? c/sx : r/sy) % 2 === 1;
    if (mv && landed) continue;
    let bc = c, br = r, bw = sx, bh = sy;
    if (mv) { if (vert) bc -= sx*m; else br -= sy*m; }
    else if (landed) { if (vert) bw = lerp(sx, 2*sx, q); else bh = lerp(sy, 2*sy, q); }
    const [x, y, cw, ch] = blockRect(camr, bc, br, bw, bh);
    if (offscreen(x, y, cw, ch)) continue;
    const a = u < R0 && !(c === MID && r === MID) ? others : 1;
    if (a <= 0) continue;
    if (mv) { cx.fillStyle = BG; cx.fillRect(x, y, cw, ch); }      // a halo: the mover is a tile on top
    if (mv || !landed) { cellBox(x, y, cw, ch, fill, a); cellText(val, x, y, cw, ch, a, TINK); continue; }
    const px = x - (pop - 1)*cw/2, py = y - (pop - 1)*ch/2, pw = cw*pop, ph = ch*pop;
    cellBox(px, py, pw, ph, lit, a); cellText(val2, px, py, pw, ph, a, TINK);
  }
  cx.globalAlpha = ease((u - RDONE - 0.5)/0.4);
  T("Final result!", W/2, 660, 24, GREEN, "center", true);
  cx.globalAlpha = 1;
};

// ------------------------------------------------------------------- beats
// ~ is a dim aside in smaller type, % a full-size line in dim ink, # is a
// title, "" is a breath of space
function sayLines(b) {
  return b.slice(2).filter(s => !TAG.has(s)).map(s => s[0] === "~"
    ? { s: s.slice(1), size: 22, pitch: 40, color: DIM }
    : s[0] === "%" ? { s: s.slice(1), size: 34, pitch: 62, color: DIM }
    : s[0] === "#" ? { s: "*" + s.slice(1).replace(/([,.:;!?]*)$/, "*$1"), size: 44, pitch: 78, color: INK }
    : s[0] === "/" ? { s: s.slice(1), size: 30, pitch: 56, color: INK, slant: true }
    : s === "" ? { s, size: 34, pitch: 30, color: INK }
    : { s, size: 34, pitch: 62, color: INK });
}
// a slide too wide or too tall for the screen shrinks as a whole, so its
// lines keep their proportions. Lines are centred, or share a left edge
// when the slide is tagged left (the block itself stays centred).
S.say = (u, dur, b) => {
  const ls = sayLines(b), L = b.includes(left), tint = b.includes(red) ? RED : b.includes(green) ? GREEN : null;
  const gap = (i, k) => k*((ls[i - 1].pitch + ls[i].pitch)/2 + (ls[i - 1].size === 22 && ls[i].size !== 22 ? 18 : 0));
  const ws = ls.map(l => { font(l.size, true); return cx.measureText(l.s.replace(/[*+/]/g, "")).width; });
  let k = Math.min(1, (W - 120)/Math.max(...ws)), hgt = 0;
  ls.forEach((l, i) => { if (i) hgt += gap(i, 1); });
  k = Math.min(k, (H - 130)/hgt);
  let y = 372 - hgt*k/2 + 12*k;
  const x0 = W/2 - Math.max(...ws)*k/2;
  ls.forEach((l, i) => {
    if (i) y += gap(i, k);
    cx.globalAlpha = i === 0 ? 1 : ease((u - b.at[i])/0.4);
    if (l.slant) { cx.save(); cx.transform(1, 0, -0.2, 1, 0.2*y, 0); }
    rich(l.s, L ? x0 + ws[i]*k/2 : W/2, y, l.size*k, tint || l.color);
    if (l.slant) cx.restore();
    cx.globalAlpha = 1;
  });
};

// a name written piece by piece: each part lands after the one before
// it, the whole centred where it will end
S.reveal = (u, dur, b) => {
  const parts = b[2].split("|"), size = b[3], bold = size >= 44;
  font(size, bold);
  const ws = parts.map(p => cx.measureText(p).width);
  let x = W/2 - ws.reduce((a, w) => a + w, 0)/2;
  parts.forEach((p, i) => {
    cx.globalAlpha = ease((u - i*0.9)/0.4);
    T(p, x, 372 + size*0.36, size, INK, "left", bold);
    x += ws[i]; cx.globalAlpha = 1;
  });
};

S.end = (u, dur) => {
  T("Bend", W/2, 290, 64, INK, "center", true);
  cx.globalAlpha = ease((u - 0.6)/0.5);
  T("fast  ·  scalable  ·  no mistakes", W/2, 360, 24, GREEN, "center");
  cx.globalAlpha = ease((u - 1.8)/0.5);
  T("Python syntax · C speed · CPU and GPU · proofs", W/2, 430, 19, DIM, "center");
  T("github.com/HigherOrderCO/Bend", W/2, 480, 22, "#1a5fd0", "center");
  cx.globalAlpha = 1;
};

// ------------------------------------------------------------------ pacing
// Sentence beats size themselves: line i lands once line i-1 has been read,
// and the beat ends one breath after the last line. Picture beats get the
// seconds their motion needs plus a hold.
const FIXED = { check: 10.5, bench: 9.5, par: 10.5, dist: DALL + 1.5, eval: EDONE + 1.9,
                reduce: RDONE + 3.2, laws: 12.0, intro: 8.0, walk: 6.3, block: 5.8, end: 24.0 };
for (const b of BEATS) {
  if (b[0] === "say") {
    const ls = b.slice(1).filter(s => !TAG.has(s));
    let t = 0; b.at = ls.map(s => { const a = t; t += READ*cost(s) + 0.4; return a; });
    const d = b.includes(quick) ? t + 0.3 : (t*1.25 + 0.8)*(b.includes(punch) ? 1.3 : 1);
    b.splice(1, 0, Math.max(2.4, d));
  } else b.splice(1, 0, b[0] === "reveal" ? 0.9*(b[1].split("|").length - 1) + 3.4 : FIXED[b[0]]);
}
const T0 = []; let DUR = 0;
for (const b of BEATS) { T0.push(DUR); DUR += b[1]; }
const SCENES = BEATS.map(b => [b[0] === "say"
  ? "“" + b[2].replace(/[*+~#%/]/g, "") : b[0] + (b[2] && !TAG.has(b[2]) ? " " + b[2] : ""), b[1]]);

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
