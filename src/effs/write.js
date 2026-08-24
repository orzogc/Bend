// IO
// ==
//! use ./sys.js

function io_write(text) {
  const data = [];
  for (const c of text) {
    data.push(c.codePointAt(0) & 255);
  }
  io_out(1, Uint8Array.from(data));
  return { $: "Unit" };
}
