// Counts the flattened pattern matches (Mat nodes) of an eval's solution:
// every def written after the "# solution" line. Fails on an incomplete or
// unsafe file. usage: bun evals/count.ts <file.bend>
import * as fs from "fs";
import * as path from "path";
import * as Bend from "../bend2/bend.ts";

function mats(t: unknown): number {
  if (t === null || typeof t !== "object") return 0;
  const o = t as Record<string, unknown>;
  let n = o.$ === "Mat" ? 1 : 0;
  for (const k in o) {
    const v = o[k] as Record<string, unknown> | null;
    if (v !== null && typeof v === "object" && v.src === undefined) n += mats(v);
  }
  return n;
}

const file = path.resolve(process.argv[2]);
const src  = fs.readFileSync(file, "utf8");
const at   = src.indexOf("\n# solution");
if (at < 0) { console.error("no '# solution' line"); process.exit(1); }
const mine = new Set([...src.slice(at).matchAll(/^def ([^\s(:]+)/gm)].map(m => m[1]));
const book = Bend.book_nil();
try {
  await Bend.book_load(book, file, "", new Map());
  Bend.book_valid(book);
} catch (e) {
  const err = e as Bend.Err;
  console.error(err?.$ === "Err" ? Bend.err_show(err) : String(e));
  process.exit(1);
}
const bad = Object.entries(book.tlds).filter(([_, t]) => t.$ === "Def" && (t.u || (t.v === null && !t.b && !t.i))).map(([k]) => k);
if (book.hols || bad.length) { console.error("incomplete or unsafe:", book.hols, bad.join(" ")); process.exit(1); }
let total = 0;
for (const [k, t] of Object.entries(book.tlds)) {
  if (t.$ === "Def" && t.v !== null && mine.has(k)) {
    const n = mats(Bend.term_lower(t.v));
    total += n;
    console.log(n, k);
  }
}
console.log(total);
