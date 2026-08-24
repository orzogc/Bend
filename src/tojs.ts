// Bend → JavaScript
// ==================
//
// Compiles a checked Book into one standalone JS program: the runtime.js
// text, one function per def, then the main call. Compilation walks each
// def's elaboration (def.e: an Ann on every layer), reading types off the
// Anns. A term compiles toward a destination: a JS variable, a return, or
// an expression handed back (statement-shaped parts hoist). Binders
// consume a queue of pending argument terms; a HOAS body is applied to a
// Var whose name IS the emitted JS, so a variable compiles to itself and
// an emitted expression re-enters the queue as a Var. NATIVES maps base
// types to plain JS formats; other ADTs become {$: "K", $0, ...}. Erased
// binders, args and fields drop. Emitted names carry a '$', which no Bend
// name and no runtime function contains; an intrinsic def's saturated
// name is its runtime function.

import * as fs from "fs";
import * as core from "./core.ts";

// Types
// =====

// File: the output state: the book, the lines emitted so far, the per-def
// local-name counts, and the enclosing tail loop (null inside closures).
export type File = {
  book:  core.Book;
  lines: string[];
  fresh: Map<string, number>;
  loop:  { name: core.Name; args: string[] } | null;
};

// Native: per ctor, how to build (intr), read (elim) and test (cond) the
// type's JS format.
export type Native = {
  intr: Record<core.Name, (xs: string[]) => string>;
  elim: Record<core.Name, (s: string) => string[]>;
  cond: Record<core.Name, (s: string) => string>;
};

// Constants
// =========

export const RUNTIME: string = fs.readFileSync(new URL("./runtime.js", import.meta.url), "utf8");

// The runtime's functions, scraped from its text: the intrinsic def names.
export const INTRINSICS: Set<string> = new Set([...RUNTIME.matchAll(/^function (\w+)/gm)].map((m) => m[1]));

export const NATIVES: Record<core.Name, Native> = {
  Nat: {
    intr: {
      Zero: () => "0n",
      Succ: ([p]) => {
        if (/^\d+n$/.test(p)) {
          return (BigInt(p.slice(0, -1)) + 1n) + "n";
        }
        return "(" + p + " + 1n)";
      },
    },
    elim: {
      Zero: () => [],
      Succ: (s) => ["(" + s + " - 1n)"],
    },
    cond: {
      Zero: (s) => s + " === 0n",
      Succ: (s) => s + " !== 0n",
    },
  },
  Bool: {
    intr: {
      False: () => "false",
      True: () => "true",
    },
    elim: {
      False: () => [],
      True: () => [],
    },
    cond: {
      False: (s) => "!" + s,
      True: (s) => s,
    },
  },
  U32: {
    intr: {
      U32: ([w]) => "word_to_u32(" + w + ")",
    },
    elim: {
      U32: (s) => ["u32_to_word(" + s + ")"],
    },
    cond: {},
  },
  Char: {
    intr: {
      Chr: ([c]) => {
        const n = Number(c);
        if (/^\d+$/.test(c) && (n < 0xd800 || (n >= 0xe000 && n <= 0x10ffff))) {
          return JSON.stringify(String.fromCodePoint(n));
        }
        return "char_new(" + c + ")";
      },
    },
    elim: {
      Chr: (s) => ["char_code(" + s + ")"],
    },
    cond: {},
  },
  String: {
    intr: {
      SNil: () => "\"\"",
      SCon: ([h, t]) => {
        if (STRLIT.test(h) && STRLIT.test(t)) {
          return JSON.stringify(JSON.parse(h) + JSON.parse(t));
        }
        return "(" + h + " + " + t + ")";
      },
    },
    elim: {
      SNil: () => [],
      SCon: (s) => ["string_head(" + s + ")", "string_tail(" + s + ")"],
    },
    cond: {
      SNil: (s) => s + " === \"\"",
      SCon: (s) => s + " !== \"\"",
    },
  },
  Array: {
    intr: {
      ALeaf: ([v]) => "[" + v + "]",
      ANode: ([l, r]) => "array_node(" + l + ", " + r + ")",
    },
    elim: {
      ALeaf: (s) => [s + "[0]"],
      ANode: (s) => ["array_left(" + s + ")", "array_right(" + s + ")"],
    },
    cond: {
      ALeaf: (s) => s + ".length === 1",
      ANode: (s) => s + ".length !== 1",
    },
  },
};

const IDENT  = /^[A-Za-z_$][A-Za-z0-9_$]*$/;
const STRLIT = /^"(?:[^"\\]|\\.)*"$/;

// File
// ====

export function file_push(fl: File, tab: number, line: string): void {
  fl.lines.push("  ".repeat(tab) + line);
}

// file_fresh: the JS local for binder k: a '$' plus its per-def use count.
export function file_fresh(fl: File, k: core.Name): string {
  const n = fl.fresh.get(k) ?? 0;
  fl.fresh.set(k, n + 1);
  return k.replace(/\./g, "$") + "$" + n;
}

// Term
// ====

// term_is_tail_call: does the raw def body reach a saturated self call in
// tail position? d is the binder depth: core identifies vars by it.
export function term_is_tail_call(tm: core.HTerm, k: core.Name, n: number, d: number = 0): boolean {
  const t = core.term_strip(tm);
  switch (t.$) {
    case "Lam":
    case "Let": {
      const f = term_is_tail_call(t.f(core.Var(t.k, d)), k, n, d + 1);
      return f;
    }
    case "Mat": {
      const h = term_is_tail_call(t.h, k, n, d);
      const m = term_is_tail_call(t.m, k, n, d);
      return h || m;
    }
    case "Rwt": {
      const f = term_is_tail_call(t.f, k, n, d);
      return f;
    }
    case "App": {
      let args = 0;
      let cur: core.HTerm = t;
      while (cur.$ === "App") {
        args += 1;
        cur = core.term_strip(cur.f);
      }
      if (cur.$ === "Ref") {
        return cur.k === k && args === n;
      }
      if (cur.$ === "Mat" || cur.$ === "Lam" || cur.$ === "Let" || cur.$ === "Rwt") {
        const f = term_is_tail_call(cur, k, n, d);
        return f;
      }
      return false;
    }
    default: {
      return false;
    }
  }
}

// term_get_tele: the [name, quant] pairs of a type's All spine.
export function term_get_tele(book: core.Book, tm: core.HTerm): Array<[core.Name, core.Quant]> {
  const out: Array<[core.Name, core.Quant]> = [];
  let t = core.term_wnf(book, tm);
  while (t.$ === "All") {
    out.push([t.k, t.q]);
    t = core.term_wnf(book, t.B(core.Var(t.k, out.length - 1)));
  }
  return out;
}

// Def
// ===

// def_get_params: the def's parameter [name, quant] pairs.
export function def_get_params(book: core.Book, def: core.Def): Array<[core.Name, core.Quant]> {
  const tele = term_get_tele(book, def.T);
  if (tele.length < def.n) {
    throw new Error("tojs: a def type shorter than its parameters");
  }
  return tele.slice(0, def.n);
}

// Ctr
// ===

// ctr_get_quants: the constructor's field quantities (its telescope's
// last ctr.n entries).
export function ctr_get_quants(book: core.Book, ctr: core.Ctr): core.Quant[] {
  const tele = term_get_tele(book, ctr.T);
  return tele.slice(tele.length - ctr.n).map(([_, q]) => q);
}

// Compile
// =======

// compile_name: the curried JS name of a def: '$'-prefixed, '.' → '$'.
export function compile_name(k: core.Name): string {
  return "$" + k.replace(/\./g, "$");
}

// compile_name_sat: the saturated JS name: the runtime function for an
// intrinsic, else a '$' suffix.
export function compile_name_sat(k: core.Name): string {
  const low = k.toLowerCase().replace(/\./g, "_");
  return INTRINSICS.has(low) ? low : compile_name(k) + "$";
}

// compile_term: emit one checked term at indentation tab, toward tgt: a
// JS variable, "return", or null to get the expression handed back. d is
// the binder depth: core identifies vars by it, so it must stay fresh.
export function compile_term(fl: File, tm: core.HTerm, ty: core.HTerm | null, tab: number, tgt: string | null, q: core.HTerm[], d: number): string {
  // compile_term_put: finish with expression e in the requested position.
  function compile_term_put(e: string): string {
    if (tgt !== null) {
      file_push(fl, tab, (tgt === "return" ? "return " + e : tgt + " = " + e) + ";");
    }
    return e;
  }

  // compile_term_body: a closure body: its own lines, no enclosing loop;
  // one plain return collapses to the arrow expression.
  function compile_term_body(bm: core.HTerm, bty: core.HTerm | null, bq: core.HTerm[], bd: number): string {
    const lines = fl.lines;
    const loop  = fl.loop;
    fl.lines = [];
    fl.loop  = null;
    compile_term(fl, bm, bty, tab + 1, "return", bq, bd);
    const body = fl.lines;
    fl.lines = lines;
    fl.loop  = loop;
    if (body.length === 1 && body[0].trim().startsWith("return ")) {
      const e = body[0].trim().slice("return ".length, -1);
      if (e.startsWith("{")) {
        return "(" + e + ")";
      }
      return e;
    }
    return "{\n" + body.join("\n") + "\n" + "  ".repeat(tab) + "}";
  }

  // compile_term_match: emit a case tree over the queue's head scrutinee.
  function compile_term_match(x: core.HTerm, T: core.HTerm | null): void {
    // compile_term_match_arm: one arm: queue the live field exprs for its
    // binder telescope.
    function compile_term_match_arm(h: core.HTerm, k: core.Name, tab2: number, native: Native | undefined): void {
      const ctr = fl.book.ctrs[k];
      if (ctr === undefined) {
        throw new Error("tojs: unknown constructor: " + k);
      }
      let fields: string[];
      if (native !== undefined) {
        fields = native.elim[k](s);
      } else {
        fields = [];
        const live = ctr_get_quants(fl.book, ctr).filter((u) => u.$ !== "None").length;
        for (let j = 0; j < live; j++) {
          fields.push(s + ".$" + j);
        }
      }
      const args: core.HTerm[] = fields.map((f) => core.Var(f, 0));
      compile_term(fl, h, null, tab2, tgt, [...args, ...rest], d);
    }

    let s = compile_term(fl, q[0], null, tab, null, [], d);
    if (!IDENT.test(s)) {
      const t = file_fresh(fl, "$t");
      file_push(fl, tab, "const " + t + " = " + s + ";");
      s = t;
    }
    const rest: core.HTerm[] = q.slice(1).map((a) => core.Var(compile_term(fl, a, null, tab, null, [], d), 0));
    if (x.$ === "Efq") {
      file_push(fl, tab, "throw new Error(\"unreachable\");");
      return;
    }
    const all = T === null ? null : core.term_wnf(fl.book, T);
    if (all === null || all.$ !== "All") {
      throw new Error("tojs: a match without a function-typed Ann");
    }
    const adt = core.term_wnf(fl.book, all.A);
    if (adt.$ !== "ADT") {
      throw new Error("tojs: a non-datatype match scrutinee");
    }
    const arms: Array<[core.Name, core.HTerm]> = [];
    let cur: core.HTerm = x;
    let m = core.term_strip(cur);
    while (m.$ === "Mat") {
      arms.push([m.k, m.h]);
      cur = m.m;
      m = core.term_strip(cur);
    }
    let end: core.HTerm | null = null;
    if (m.$ !== "Efq") {
      end = cur;
    }
    const tld = fl.book.tlds[adt.k];
    if (tld === undefined || tld.$ !== "ADT") {
      throw new Error("tojs: undeclared datatype: " + adt.k);
    }
    if (arms.length === 0 && end !== null) {
      compile_term(fl, end, null, tab, tgt, [core.Var(s, 0), ...rest], d);
      return;
    }
    const total = tld.c.length - adt.r.length;
    if (arms.length === total) {
      end = null;
    }
    const native = NATIVES[adt.k];
    if (arms.length === 1 && end === null && total === 1) {
      compile_term_match_arm(arms[0][1], arms[0][0], tab, native);
      return;
    }
    for (let i = 0; i < arms.length; i++) {
      let cond: string;
      if (native !== undefined) {
        cond = native.cond[arms[i][0]](s);
      } else {
        cond = s + ".$ === \"" + arms[i][0] + "\"";
      }
      let open = "} else if (" + cond + ") {";
      if (i === 0) {
        open = "if (" + cond + ") {";
      } else if (end === null && i === arms.length - 1) {
        open = "} else {";
      }
      file_push(fl, tab, open);
      compile_term_match_arm(arms[i][1], arms[i][0], tab + 1, native);
    }
    if (end !== null) {
      file_push(fl, tab, "} else {");
      compile_term(fl, end, null, tab + 1, tgt, [core.Var(s, 0), ...rest], d);
    }
    file_push(fl, tab, "}");
  }

  const x = core.term_force(tm);
  switch (x.$) {
    case "Ann": {
      const e = compile_term(fl, x.x, x.T, tab, tgt, q, d);
      return e;
    }
    case "Var": {
      let e = x.k;
      for (const a of q) {
        e += "(" + compile_term(fl, a, null, tab, null, [], d) + ")";
      }
      return compile_term_put(e);
    }
    case "Ref": {
      const tld = fl.book.tlds[x.k];
      if (tld === undefined) {
        throw new Error("tojs: unknown name: " + x.k);
      }
      if (tld.$ === "ADT") {
        return compile_term_put("null");
      }
      const live  = def_get_params(fl.book, tld).filter(([_, u]) => u.$ !== "None").length;
      const exprs = q.map((a) => compile_term(fl, a, null, tab, null, [], d));
      const lp    = fl.loop;
      if (tgt === "return" && lp !== null && lp.name === x.k && exprs.length === live) {
        const moves: Array<[string, string]> = [];
        for (let i = 0; i < exprs.length; i++) {
          if (exprs[i] !== lp.args[i]) {
            const t = file_fresh(fl, "$t");
            file_push(fl, tab, "const " + t + " = " + exprs[i] + ";");
            moves.push([lp.args[i], t]);
          }
        }
        for (const [p, t] of moves) {
          file_push(fl, tab, p + " = " + t + ";");
        }
        file_push(fl, tab, "continue;");
        return "";
      }
      let e: string;
      if (exprs.length < live) {
        e = compile_name(x.k);
        for (const a of exprs) {
          e += "(" + a + ")";
        }
      } else {
        e = compile_name_sat(x.k) + "(" + exprs.slice(0, live).join(", ") + ")";
        for (const a of exprs.slice(live)) {
          e += "(" + a + ")";
        }
      }
      return compile_term_put(e);
    }
    case "App": {
      const f = core.term_force(x.f);
      if (f.$ !== "Ann") {
        throw new Error("tojs: missing Ann on a call head");
      }
      const all = core.term_wnf(fl.book, f.T);
      if (all.$ !== "All") {
        throw new Error("tojs: a non-function call head");
      }
      const e = compile_term(fl, x.f, null, tab, tgt, all.q.$ === "None" ? q : [x.x, ...q], d);
      return e;
    }
    case "Ctr": {
      const adt = ty === null ? null : core.term_wnf(fl.book, ty);
      if (adt === null || adt.$ !== "ADT") {
        throw new Error("tojs: a Ctr without a datatype-typed Ann: " + x.k);
      }
      if (adt.k === "U32") {
        const u = core.u32_from_term(x);
        if (u !== null) {
          return compile_term_put(String(u));
        }
      }
      const ctr = fl.book.ctrs[x.k];
      if (ctr === undefined) {
        throw new Error("tojs: unknown constructor: " + x.k);
      }
      const qs = ctr_get_quants(fl.book, ctr);
      const exprs: string[] = [];
      for (let j = 0; j < x.x.length; j++) {
        if (qs[j].$ !== "None") {
          exprs.push(compile_term(fl, x.x[j], null, tab, null, [], d));
        }
      }
      const native = NATIVES[adt.k];
      if (native !== undefined) {
        return compile_term_put(native.intr[x.k](exprs));
      }
      if (exprs.length === 0) {
        return compile_term_put("$$" + x.k.replace(/\./g, "$"));
      }
      let e = "{$: \"" + x.k + "\"";
      for (let j = 0; j < exprs.length; j++) {
        e += ", $" + j + ": " + exprs[j];
      }
      return compile_term_put(e + "}");
    }
    case "Lam": {
      const all = ty === null ? null : core.term_wnf(fl.book, ty);
      if (all === null || all.$ !== "All") {
        throw new Error("tojs: a Lam without a function-typed Ann");
      }
      if (all.q.$ === "None") {
        const e = compile_term(fl, x.f(core.Var("null", d)), null, tab, tgt, q, d + 1);
        return e;
      }
      if (q.length === 0) {
        const name = file_fresh(fl, x.k);
        const body = compile_term_body(x.f(core.Var(name, d)), null, [], d + 1);
        return compile_term_put("(" + name + ") => " + body);
      }
      let name = compile_term(fl, q[0], null, tab, null, [], d);
      if (!IDENT.test(name)) {
        const alias = file_fresh(fl, x.k);
        file_push(fl, tab, "const " + alias + " = " + name + ";");
        name = alias;
      }
      const e = compile_term(fl, x.f(core.Var(name, d)), null, tab, tgt, q.slice(1), d + 1);
      return e;
    }
    case "Mat":
    case "Efq": {
      if (q.length === 0) {
        const s = file_fresh(fl, "$t");
        const body = compile_term_body(x, ty, [core.Var(s, 0)], d);
        return compile_term_put("(" + s + ") => " + body);
      }
      if (tgt === null) {
        const t = file_fresh(fl, "$t");
        file_push(fl, tab, "let " + t + ";");
        compile_term(fl, x, ty, tab, t, q, d);
        return t;
      }
      compile_term_match(x, ty);
      return "";
    }
    case "Let": {
      if (x.q.$ === "None") {
        const e = compile_term(fl, x.f(core.Var("null", d)), null, tab, tgt, q, d + 1);
        return e;
      }
      const name = file_fresh(fl, x.k);
      const v = compile_term(fl, x.v, null, tab, null, [], d);
      file_push(fl, tab, "const " + name + " = " + v + ";");
      const e = compile_term(fl, x.f(core.Var(name, d)), null, tab, tgt, q, d + 1);
      return e;
    }
    case "Rwt": {
      const e = compile_term(fl, x.f, null, tab, tgt, q, d);
      return e;
    }
    case "Rfl":
    case "Typ":
    case "All":
    case "ADT":
    case "Eql": {
      return compile_term_put("null");
    }
    default: {
      throw new Error("tojs: cannot compile a " + x.$ + " node");
    }
  }
}

// compile_def: the saturated function (a while(true) when a self tail
// call exists) plus the curried redirector; an intrinsic keeps only the
// redirector.
export function compile_def(fl: File, def: core.Def, k: core.Name): void {
  fl.fresh = new Map();
  const params: string[] = [];
  for (const [n, q] of def_get_params(fl.book, def)) {
    if (q.$ !== "None") {
      params.push(file_fresh(fl, n));
    }
  }
  const sat = compile_name_sat(k);
  const redir = "const " + compile_name(k) + " = " + params.map((p) => "(" + p + ") => ").join("") + sat + "(" + params.join(", ") + ");";
  if (INTRINSICS.has(sat)) {
    if (params.length > 0) {
      file_push(fl, 0, redir);
      file_push(fl, 0, "");
    }
    return;
  }
  if (def.v === null) {
    return;
  }
  if (def.e === undefined) {
    throw new Error("tojs: unelaborated def " + k + ": run book_valid first");
  }
  const args: core.HTerm[] = params.map((p) => core.Var(p, 0));
  if (term_is_tail_call(def.v, k, def.n)) {
    const carry = params.map((p) => file_fresh(fl, "$c"));
    file_push(fl, 0, "function " + sat + "(" + carry.join(", ") + ") {");
    fl.loop = { name: k, args: carry };
    file_push(fl, 1, "while (true) {");
    if (params.length > 0) {
      file_push(fl, 2, "const " + params.map((p, i) => p + " = " + carry[i]).join(", ") + ";");
    }
    compile_term(fl, def.e, null, 2, "return", args, 0);
    file_push(fl, 1, "}");
  } else {
    file_push(fl, 0, "function " + sat + "(" + params.join(", ") + ") {");
    fl.loop = null;
    compile_term(fl, def.e, null, 1, "return", args, 0);
  }
  file_push(fl, 0, "}");
  if (params.length > 0) {
    file_push(fl, 0, redir);
  }
  file_push(fl, 0, "");
}

// compile_book: a checked book into one runnable JS program, each
// nullary constructor of a non-native ADT getting an upfront singleton.
export function compile_book(book: core.Book): string {
  const fl: File = { book, lines: [], fresh: new Map(), loop: null };
  const seen = new Set<core.Name>();
  for (const k of book.order) {
    if (!seen.has(k)) {
      seen.add(k);
      const tld = book.tlds[k];
      if (tld.$ === "ADT" && NATIVES[k] === undefined) {
        for (const ctr of tld.c) {
          if (ctr_get_quants(book, ctr).every((u) => u.$ === "None")) {
            file_push(fl, 0, "const $$" + ctr.k.replace(/\./g, "$") + " = {$: \"" + ctr.k + "\"};");
          }
        }
      }
      if (tld.$ === "Def") {
        compile_def(fl, tld, k);
      }
    }
  }
  let out = RUNTIME + "// Program\n// =======\n\n" + fl.lines.join("\n");
  const main = book.tlds["main"];
  if (main !== undefined) {
    if (main.$ !== "Def" || main.v === null || def_get_params(book, main).some(([, u]) => u.$ !== "None")) {
      throw new Error("tojs: main must be a filled def with no live parameters (the runner calls it with none)");
    }
    out += "\nconsole.log(value_show(" + compile_name_sat("main") + "()));";
  }
  return out;
}
