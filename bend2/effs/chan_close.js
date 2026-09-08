// Chan
// ====
//! use ./chan.js

function chan_close(handle) {
  const row = chan_at(handle);
  if (row !== null && !row.shut) {
    chan_shut(handle, row);
  }
  return { $: "Unit" };
}
