// HUMAN NOTE: this particular file is AI written and nobody really cares.

import * as child from "node:child_process";
import * as fs from "node:fs";

import * as Bend from "./bend.ts";
import * as Comp from "./comp.ts";

// Main
// ====

// Constants
// =========

const USAGE = "usage: bend <file.bend> [--check | -o <bin> | --to <out.c|.js>]";

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

  const book = Bend.book_nil();
  try {
    await Bend.book_load(book, path, "", new Map());
    Bend.book_valid(book);
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
    const err = e as Bend.Err;
    console.log(err?.$ === "Err" ? Bend.err_show(err) : String(e));
    process.exit(1);
  }
}

function cli_build(bin: string): void {
  const cpu = ["-std=c11", "-O3", bin + ".c", "-lpthread", "-o", bin];
  const gpu = process.platform === "darwin"
    ? ["-DBEND_METAL=1", "-x", "objective-c", "-fobjc-arc", ...cpu,
      "-framework", "Metal", "-framework", "Foundation"]
    : ["-DBEND_CUDA=1", "-I/usr/local/cuda/include",
      "-L/usr/local/cuda/lib64", ...cpu, "-lcuda", "-lnvrtc"];
  if (child.spawnSync("cc", gpu, { stdio: "ignore" }).status !== 0
    && child.spawnSync("cc", cpu, { stdio: "inherit" }).status !== 0) {
    cli_fail("cc failed to build " + bin);
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

if (import.meta.main) {
  await cli();
}
