#!/usr/bin/env bun
// bend4-core: the minimal CLI over core.ts.
//
// Usage: bend4-core <file.bend4>
//
// Parses and checks the file, reporting the first error. When the book
// declares a `main` def, prints its strong normal form.

import * as core from "./core.ts";
import * as fs from "fs";

const path = process.argv[2];
if (path === undefined) {
  console.error("Usage: bend4-core <file.bend4>");
  process.exit(1);
}

let book: core.Book = core.book_nil();
try {
  const src = fs.readFileSync(path, "utf8");
  book = core.parse_book(src);
  core.book_valid(book);
  const main = book.tlds["main"];
  if (main !== undefined) {
    const snf = core.term_snf(book, core.Ref("main"));
    console.log(core.term_show(core.term_lower(snf)));
  }
} catch (e) {
  if (e !== null && typeof e === "object" && (e as core.Err).$ === "Err") {
    console.log(core.err_show(book, e as core.Err));
  } else {
    console.log(String(e));
  }
  process.exit(1);
}
