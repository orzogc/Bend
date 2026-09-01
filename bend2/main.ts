// HUMAN NOTE: this particular file is AI written and nobody really cares.

import * as fs from "node:fs";

import * as Bend from "./bend.ts";
import * as Comp from "./comp.ts";

// Main
// ====

// Constants
// =========

const USAGE = "usage: bend <file.bend> [--check | --to <out.c|out.js>]";

// CLI
// ===

async function cli(): Promise<void> {
  const [path, flag, to] = process.argv.slice(2);
  if (path === undefined || path === "--help") {
    console.log(USAGE);
    process.exit(path === undefined ? 1 : 0);
  }
  if (path.startsWith("--")) {
    cli_fail("unknown option " + path);
  }
  if (flag !== undefined && flag !== "--to" && flag !== "--check") {
    cli_fail("unknown option " + flag);
  }
  if (flag === "--to" && to === undefined) {
    cli_fail("--to needs an output file");
  }
  if (flag === "--check" && to !== undefined) {
    cli_fail("too many arguments");
  }
  if (to !== undefined && !to.endsWith(".c") && !to.endsWith(".js")) {
    cli_fail("--to expects a .c or a .js file, not " + to);
  }
  if (process.argv.length > 5) {
    cli_fail("too many arguments");
  }

  const book = Bend.book_nil();
  try {
    await Bend.book_load(book, path, "", new Map());
    Bend.book_valid(book);
    if (to !== undefined) {
      if (book.hols > 0) {
        console.log("Error: the book has TODOs and cannot compile");
        process.exit(1);
      }
      const emit = to.endsWith(".c") ? Comp.compile_book : Comp.js_book;
      fs.writeFileSync(to, emit(book));
    } else if (flag === "--check" || book.tlds["main"] === undefined) {
      cli_report(book);
    } else if (Comp.io_type(book) !== null) {
      process.exit(Comp.io_run(book));
    } else {
      const snf = Bend.term_snf(book, Bend.Ref("main"));
      console.log(Bend.term_show(Bend.term_lower(snf)));
    }
  } catch (e) {
    if (e !== null && typeof e === "object" && (e as Bend.Err).$ === "Err") {
      console.log(Bend.err_show(e as Bend.Err));
    } else {
      console.log(String(e));
    }
    process.exit(1);
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
