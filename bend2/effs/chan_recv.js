// Chan
// ====
//! use ./chan.js

function chan_recv(handle, k) {
  const row = chan_at(handle);
  if (row === null) {
    return { $: "None" };
  }
  if (row.ring.length > 0) {
    const v = chan_take(row);
    if (row.shut && row.ring.length === 0) {
      sys_get().kill(handle);
    }
    return { $: "Some", value: v };
  }
  if (row.wait.length > 0 && row.wait[0].item !== null) {
    return { $: "Some", value: chan_wake(row, true) };
  }
  if (row.shut) {
    sys_get().kill(handle);
    return { $: "None" };
  }
  row.wait.push({ cont: k, item: null });
  return;
}
