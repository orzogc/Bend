// IO
// ==

function io_print_err(text) {
  const data = [];
  for (const c of text) {
    data.push(c.codePointAt(0) & 255);
  }
  data.push(10);
  io_out(2, Uint8Array.from(data));
  return { $: "Unit" };
}
