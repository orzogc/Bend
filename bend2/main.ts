#!/usr/bin/env bun
// HUMAN NOTE: this particular file is AI written and nobody really cares.
//
// Run, this file is the CLI. Imported, it is the loader that makes `import
// Game from "./x.bend"` work: a bun plugin (preload it in bunfig.toml, list
// it under [serve.static] plugins, or hand it to Bun.build) and a node hook
// (node --import). A .bend module exports every filled, non-base, non-IO
// def, wrapped so a JS caller passes the live arguments, in one call or
// curried, and gets a plain value back: a constructor is {$: "Name", field:
// value, ...}, a closure is a function, Nat is BigInt, Bool, String and U32
// are native. A page bundles through Bun.build with the loader on, since
// the bun build CLI takes no plugins.

import * as child from "node:child_process";
import * as fs from "node:fs";
import * as mod from "node:module";
import * as path from "node:path";
import * as url from "node:url";
import * as thr from "node:worker_threads";

import type { BunPlugin } from "bun";

import * as Bend from "./bend.ts";
import * as Comp from "./comp.ts";

// Main
// ====

// Constants
// =========

const USAGE = "usage: bend <file.bend> [--checkup] [-o <out>]..."
  + "\n       bend <page.html> -o <dir>";

const BASE = fs.realpathSync(path.join(import.meta.dirname, "base.bend"));

export const METAL = ["-DBEND_METAL=1", "-x", "objective-c", "-fobjc-arc",
  "-fmodules"];

const PLUGIN: BunPlugin = {
  name: "bend",
  setup(build) {
    build.onLoad({ filter: /\.bend$/ }, async (args) =>
      ({ contents: await load_js(args.path), loader: "js" }));
  },
};

// CLI
// ===

async function cli(): Promise<void> {
  const args = process.argv.slice(2);
  const outs: string[] = [];
  let file: string | undefined;
  let checkup = false;
  for (let i = 0; i < args.length; i += 1) {
    const a = args[i];
    if (a === "--help") {
      cli_say(1, USAGE + "\n");
      process.exit(0);
    } else if (a === "--checkup") {
      checkup = true;
    } else if (a === "-o") {
      i += 1;
      outs.push(args[i] ?? cli_fail("-o needs an output file"));
    } else if (a.startsWith("-") || file !== undefined) {
      cli_fail(a.startsWith("-") ? "unknown option " + a : "too many arguments");
    } else {
      file = a;
    }
  }
  if (file === undefined) {
    cli_say(1, USAGE + "\n");
    process.exit(1);
  }
  if (file.endsWith(".html")) {
    if (outs.length !== 1 || checkup) {
      cli_fail("a page bundles with -o <dir>");
    }
    return cli_bundle(file, outs[0]);
  }
  try {
    const book = checkup ? await cli_checkup(file) : await book_read(file);
    if (outs.length === 0 && !checkup) {
      process.exit(book_run(book));
    }
    for (const out of outs) {
      cli_emit(book, out);
    }
  } catch (e) {
    cli_say(2, book_err(e) + "\n");
    process.exit(1);
  }
}

async function cli_checkup(file: string): Promise<Bend.Book> {
  const base = await book_read(BASE);
  const book = book_seed(base);
  const seen = new Map<string, string | null>([[BASE, ""]]);
  for (const raw of fs.readFileSync(file, "utf8").split("\n")) {
    const m = /^import\s+(\S+)\s+as\s+([A-Za-z_][A-Za-z0-9_]*)\s*$/
      .exec(raw.trim());
    if (m === null) {
      continue;
    }
    const at = path.join(path.dirname(file), m[1]);
    cli_say(1, "--- " + m[1] + " ---\n");
    let code = 1;
    try {
      const own = /^import Base$/m.test(fs.readFileSync(at, "utf8"));
      const one = await book_read(at, own ? base : undefined);
      if (own) {
        await Bend.book_load(book, at, m[2], seen);
      }
      code = book_run(one);
    } catch (e) {
      cli_say(2, book_err(e) + "\n");
    }
    if (code !== 0) {
      cli_say(1, "exit " + String(code) + "\n");
    }
  }
  Bend.book_valid(book, base.order.length);
  return book;
}

function cli_emit(book: Bend.Book, out: string): void {
  if (out.endsWith(".js")) {
    fs.writeFileSync(out, Comp.js_book(book));
  } else if (out.endsWith(".c")) {
    fs.writeFileSync(out, Comp.compile_book(book));
  } else {
    fs.writeFileSync(out + ".c", Comp.compile_book(book));
    cli_build(out);
  }
}

function cli_build(bin: string): void {
  const cpu = ["-std=c11", "-O3", bin + ".c", "-lpthread", "-lm", "-o", bin];
  const gpu = process.platform === "darwin" ? [...METAL, ...cpu]
    : ["-DBEND_CUDA=1", "-I/usr/local/cuda/include",
      "-L/usr/local/cuda/lib64", ...cpu, "-lcuda", "-lnvrtc"];
  const got = child.spawnSync("clang", gpu, { stdio: "pipe" });
  if (got.status !== 0) {
    cli_say(2, "bend: GPU build failed: " + String(got.stderr ?? got.error)
      .split("\n")[0] + "; building CPU-only\n");
    if (child.spawnSync("clang", cpu, { stdio: "inherit" }).status !== 0) {
      throw "Error: clang failed to build " + bin;
    }
  }
}

async function cli_bundle(page: string, dir: string): Promise<void> {
  const out = await Bun.build({
    entrypoints: [page],
    outdir: dir,
    target: "browser",
    minify: true,
    plugins: [PLUGIN],
  });
  for (const a of out.outputs) {
    cli_say(1, a.path + " (" + (a.size / 1024).toFixed(1) + "kb)\n");
  }
}

function cli_report(book: Bend.Book): void {
  const tlds = Object.values(book.tlds);
  const uns  = tlds.filter((t) => t.$ === "Def" && t.u === true).length;
  if (book.hols > 0) {
    cli_say(1, String(book.hols) + (book.hols === 1 ? " TODO" : " TODOs")
      + " found.\nThe code is incomplete, and not a valid proof yet.\n");
  } else if (uns > 0) {
    cli_say(1, String(uns) + (uns === 1 ? " term" : " terms")
      + " annotated as unsafe.\nThe code is well-typed, but may contain"
      + " logical paradoxes.\n");
  } else {
    cli_say(1, "All terms check.\n");
  }
}

function cli_say(fd: number, text: string): void {
  fs.writeSync(fd, text);
}

function cli_fail(msg: string): never {
  cli_say(2, "bend: " + msg + "\n" + USAGE + "\n");
  process.exit(1);
}

// Book
// ====

async function book_read(file: string,
  base?: Bend.Book): Promise<Bend.Book> {
  const book = base === undefined ? Bend.book_nil() : book_seed(base);
  const seen = new Map<string, string | null>(
    base === undefined ? [] : [[BASE, ""]]);
  await Bend.book_load(book, file, "", seen);
  Bend.book_valid(book, base?.order.length ?? 0);
  return book;
}

function book_seed(base: Bend.Book): Bend.Book {
  const book = Bend.book_nil();
  for (const k of Object.keys(base.tlds)) {
    book.tlds[k] = { ...base.tlds[k] };
  }
  Object.assign(book.ctrs, base.ctrs);
  for (const k of Object.keys(base.tmps)) {
    book.tmps[k] = { ...base.tmps[k], p: { ...base.tmps[k].p, book },
      is: { ...base.tmps[k].is } };
  }
  book.order.push(...base.order);
  return book;
}

function book_run(book: Bend.Book): number {
  const main = book.tlds["main"];
  if (main === undefined || main.$ !== "Def"
    || (main.v === null && main.i === undefined)) {
    cli_report(book);
    return 0;
  }
  if (Comp.io_type(book) !== null) {
    return Comp.io_run(book);
  }
  const snf = Bend.term_snf(book, main.v as Bend.HTerm);
  cli_say(1, Bend.term_show(Bend.term_lower(snf)) + "\n");
  return 0;
}

function book_err(e: unknown): string {
  const err = e as Bend.Err;
  return err?.$ === "Err" ? Bend.err_show(err) : String(e);
}

// Load
// ====

async function load_js(path: string): Promise<string> {
  let book: Bend.Book;
  try {
    book = await book_read(path);
  } catch (e) {
    throw new Error(book_err(e));
  }
  if (book.hols > 0) {
    throw new Error(path + " has TODOs and cannot compile");
  }
  const outs = [...new Set(book.order)].filter((k) => {
    const tld = book.tlds[k];
    return tld.$ === "Def" && tld.v !== null && tld.b !== true
      && tld.i === undefined && Comp.io_base(book, tld.T) === null;
  });
  return Comp.js_lib(book, outs, outs);
}

export async function load(u: string, context: unknown,
  next: (u: string, context: unknown) => unknown): Promise<unknown> {
  return u.endsWith(".bend")
    ? { format: "module", shortCircuit: true,
      source: await load_js(url.fileURLToPath(u)) }
    : next(u, context);
}

export default PLUGIN;

if (import.meta.main) {
  await cli();
} else if (typeof Bun !== "undefined") {
  Bun.plugin(PLUGIN);
} else if (thr.isMainThread) {
  mod.register(import.meta.url);
}
