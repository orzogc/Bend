// Chan
// ====
//! use ./sys.js

function chan_at(handle) {
  return sys_get().read(handle, "chan");
}

function chan_wake(row, x) {
  const w = row.wait.shift();
  io_push(w.cont, x, false);
  return w.item;
}

function chan_take(row) {
  const v = row.ring.shift();
  if (row.wait.length > 0) {
    row.ring.push(chan_wake(row, true));
  }
  return v;
}

function chan_shut(handle, row) {
  row.shut = true;
  while (row.wait.length > 0) {
    chan_wake(row, row.wait[0].item === null ? { $: "None" } : false);
  }
  if (row.ring.length === 0) {
    sys_get().kill(handle);
  }
}
