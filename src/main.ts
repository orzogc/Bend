#!/usr/bin/env bun
// bend-core: the minimal CLI over core.ts.
//
// Usage: bend-core <file.bend>             check; print main's normal form
//        bend-core <file.bend> --to <out>  compile the same book: .c → tocl,
//                                          .js → tojs

import * as core from "./core.ts";
import * as tojs from "./tojs.ts";
import * as tocl from "./tocl.ts";
import * as fs from "fs";

const USAGE = "usage: bend <file.bend> [--to <out.c|out.js>]";

function fail(msg: string): never {
  console.error("bend: " + msg + "\n" + USAGE);
  process.exit(1);
}

const [path, flag, to] = process.argv.slice(2);
if (path === undefined || path === "--help") {
  console.log(USAGE);
  process.exit(path === undefined ? 1 : 0);
}
if (path.startsWith("--")) { fail("unknown option " + path); }
if (flag !== undefined && flag !== "--to") { fail("unknown option " + flag); }
if (flag === "--to" && to === undefined) { fail("--to needs an output file"); }
if (to !== undefined && !to.endsWith(".c") && !to.endsWith(".js")) {
  fail("--to expects a .c or a .js file, not " + to);
}
if (process.argv.length > 5) { fail("too many arguments"); }

const book = core.book_nil();
try {
  core.book_load(book, path, "", new Map());
  core.book_valid(book);
  if (to !== undefined) {
    const emit = to.endsWith(".c") ? tocl.compile_book : tojs.compile_book;
    fs.writeFileSync(to, emit(book));
  } else {
    const main = book.tlds["main"];
    if (main !== undefined) {
      const snf = core.term_snf(book, core.Ref("main"));
      console.log(core.term_show(core.term_lower(snf)));
    }
  }
} catch (e) {
  if (e !== null && typeof e === "object" && (e as core.Err).$ === "Err") {
    console.log(core.err_show(e as core.Err));
  } else {
    console.log(String(e));
  }
  process.exit(1);
}
