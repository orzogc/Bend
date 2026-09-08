// Chan
// ====

function chan_close(handle) {
  const row = io_read(handle, "chan");
  if (row !== null && !row.shut) {
    chan_shut(handle, row);
  }
  return { $: "Unit" };
}
