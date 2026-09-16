// Counts every core syntax node in the bodies of defs written after an eval's
// "# solution" line. Fails on an incomplete or
// unsafe file. usage: bun evals/count.ts <file.bend>
// Eval tiers: cake 27-81, easy 82-243, firm 244-729,
// hard 730-2187, hell 2188-6561 (successive powers of three).
import * as fs from "fs";
import * as path from "path";
import * as Bend from "../bend2/bend.ts";

// Count syntax, including erased arguments, annotations and rewrite motives.
// Names, source spans, binder indices and quantity flags are metadata.
function size(t: Bend.LTerm | Bend.Patt): number {
  switch (t.$) {
    case "Var": case "Ref": case "Qnt": case "Qua":
    case "Efq": case "Rfl": case "Hol": case "PVar": return 1;
    case "Sub": return 1 + size(t.v) + size(t.f);
    case "Let": return 1 + t.v.reduce((n, v) => n + size(v), 0) + size(t.f);
    case "Typ": return 1 + size(t.g);
    case "Min": return 1 + size(t.a) + size(t.b);
    case "All": return 1 + size(t.A) + size(t.B);
    case "Lam": return 1 + size(t.f);
    case "App": return 1 + size(t.f) + size(t.x);
    case "ADT": case "Ctr": case "PCtr":
      return 1 + t.x.reduce((n, x) => n + size(x), 0);
    case "Mat": return 1 + size(t.h) + size(t.m);
    case "Eql": return 1 + size(t.a) + size(t.b) + size(t.T);
    case "Rwt": return 1 + size(t.e) + size(t.p) + size(t.f);
    case "Ann": return 1 + size(t.x) + size(t.T);
    default: {
      const unexpected: never = t;
      throw new Error(`unknown syntax node: ${JSON.stringify(unexpected)}`);
    }
  }
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
    const n = size(Bend.term_lower(t.v));
    total += n;
    console.log(n, k);
  }
}
console.log(total);
