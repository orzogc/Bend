#!/usr/bin/env bun
// bend-core: the minimal CLI over core.ts.
//
// Usage: bend-core <file.bend>             check; print main's normal form
//        bend-core <file.bend> --to <out>  compile the same book: .c → tocl,
//                                          anything else → tojs

import * as core from "./core.ts";
import * as tojs from "./tojs.ts";
import * as tocl from "./tocl.ts";
import * as fs from "fs";

const path = process.argv[2];
if (path === undefined) {
  console.error("Usage: bend-core <file.bend> [--to out.js]");
  process.exit(1);
}
const to = process.argv[3] === "--to" ? process.argv[4] : undefined;
if (process.argv[3] === "--to" && to === undefined) {
  console.error("Usage: bend-core <file.bend> [--to out.js]");
  process.exit(1);
}

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
