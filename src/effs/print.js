// IO
// ==
//! use ./sys.js

function io_print(text) {
  const data = [];
  for (const c of text) {
    data.push(c.codePointAt(0) & 255);
  }
  data.push(10);
  io_out(1, Uint8Array.from(data));
  return { $: "Unit" };
}
