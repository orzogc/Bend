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
import * as url from "node:url";
import * as thr from "node:worker_threads";

import type { BunPlugin } from "bun";

import * as Bend from "./bend.ts";
import * as Comp from "./comp.ts";

// Main
// ====

// Constants
// =========

const USAGE = "usage: bend <file.bend> [--check | -o <bin> | --to <out.c|.js>]"
  + "\n       bend <page.html> -o <dir>";

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
  const [path, flag, out, more] = process.argv.slice(2);
  if (path === undefined || path === "--help") {
    console.log(USAGE);
    process.exit(path === undefined ? 1 : 0);
  }
  const emit = flag === "--to" || flag === "-o";
  if (path[0] === "-" || (flag !== undefined && flag !== "--check" && !emit)) {
    cli_fail("unknown option " + (path[0] === "-" ? path : flag));
  }
  if (more !== undefined || (emit ? out === undefined : out !== undefined)) {
    cli_fail(emit && out === undefined
      ? flag + " needs an output file" : "too many arguments");
  }
  if (flag === "--to" && !/\.(c|js)$/.test(out)) {
    cli_fail("--to expects a .c or a .js file, not " + out);
  }
  if (path.endsWith(".html")) {
    if (flag !== "-o") {
      cli_fail("a page bundles with -o <dir>");
    }
    return cli_bundle(path, out);
  }

  try {
    const book = await book_read(path);
    if (emit) {
      if (book.hols > 0) {
        throw "Error: the book has TODOs and cannot compile";
      }
      const c = flag === "-o" || out.endsWith(".c");
      fs.writeFileSync(flag === "-o" ? out + ".c" : out,
        c ? Comp.compile_book(book) : Comp.js_book(book));
      if (flag === "-o") {
        cli_build(out);
      }
    } else if (flag === "--check" || book.tlds["main"] === undefined) {
      cli_report(book);
    } else if (Comp.io_type(book) !== null) {
      process.exit(Comp.io_run(book));
    } else {
      const snf = Bend.term_snf(book, Bend.Ref("main"));
      console.log(Bend.term_show(Bend.term_lower(snf)));
    }
  } catch (e) {
    console.error(book_err(e));
    process.exit(1);
  }
}

function cli_build(bin: string): void {
  const cpu = ["-std=c11", "-O3", bin + ".c", "-lpthread", "-lm", "-o", bin];
  const gpu = process.platform === "darwin"
    ? ["-DBEND_METAL=1", "-x", "objective-c", "-fobjc-arc", ...cpu,
      "-framework", "Metal", "-framework", "Foundation"]
    : ["-DBEND_CUDA=1", "-I/usr/local/cuda/include",
      "-L/usr/local/cuda/lib64", ...cpu, "-lcuda", "-lnvrtc"];
  if (child.spawnSync("clang", gpu, { stdio: "ignore" }).status !== 0
    && child.spawnSync("clang", cpu, { stdio: "inherit" }).status !== 0) {
    cli_fail("clang failed to build " + bin);
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
    console.log(a.path + " (" + (a.size / 1024).toFixed(1) + "kb)");
  }
}

function cli_report(book: Bend.Book): void {
  const tlds = Object.values(book.tlds);
  const uns  = tlds.filter((t) => t.$ === "Def" && t.u === true).length;
  const all  = "All " + tlds.length + " definitions check";
  if (book.hols > 0) {
    const s = book.hols === 1 ? " TODO" : " TODOs";
    console.log(all + ", with " + book.hols + s + " found.");
    console.log("The code is incomplete, and not a valid proof yet.");
  } else if (uns > 0) {
    console.log(all + ", with " + uns + " annotated as unsafe.");
    console.log("The code is well-typed, but may contain logical paradoxes.");
  } else {
    console.log(all + ".");
  }
}

function cli_fail(msg: string): never {
  console.error("bend: " + msg + "\n" + USAGE);
  process.exit(1);
}

// Book
// ====

async function book_read(path: string): Promise<Bend.Book> {
  const book = Bend.book_nil();
  await Bend.book_load(book, path, "", new Map());
  Bend.book_valid(book);
  return book;
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
  return Comp.js_lib(book, outs);
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
