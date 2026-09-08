// Chan
// ====

function chan_new(room) {
  const row = { room: Number(room), ring: [], wait: [], shut: false };
  const h = io_mint("Chan", "chan", row);
  if (h === null) {
    throw "bend: error 1: the handle table is full";
  }
  return h;
}
