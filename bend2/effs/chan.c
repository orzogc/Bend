// Chan
// ====
//! use ./sys.c

#define IO_CHAN 6

// ChanWait ::=
//   | ChanWait(cont, item, next)
typedef struct ChanWait {
  Term             cont;
  Term             item;
  struct ChanWait* next;
} ChanWait;

// ChanRow ::=
//   | ChanRow(room, size, head, shut, ring, wait, last)
typedef struct {
  uint32_t  room;
  uint32_t  size;
  uint32_t  head;
  uint32_t  shut;
  Term*     ring;
  ChanWait* wait;
  ChanWait* last;
} ChanRow;

static ChanRow* chan_at(IoHand h) {
  intptr_t row = io_sys_read(h, IO_CHAN);
  return row < 0 ? NULL : (ChanRow*)row;
}

static void chan_park(ChanRow* row, Term cont, Term item) {
  ChanWait* w = io_mem(malloc(sizeof(ChanWait)));
  w->cont = cont;
  w->item = item;
  w->next = NULL;
  if (row->wait == NULL) {
    row->wait = w;
  } else {
    row->last->next = w;
  }
  row->last = w;
}

static Term chan_wake(ChanRow* row, Term x) {
  ChanWait* w = row->wait;
  Term item = w->item;
  row->wait = w->next;
  io_push(w->cont, x, false);
  free(w);
  return item;
}

#define chan_some(e, v) io_box(e, CID_SOME, v, IO_HOTS & 32)

static Term chan_bool(bool b) {
  return term_pak(b ? CID_TRUE : CID_FALSE, 0);
}

static Term chan_take(ChanRow* row) {
  Term v = row->ring[row->head];
  row->head = (row->head + 1) % row->room;
  row->size -= 1;
  if (row->wait != NULL) {
    Term item = chan_wake(row, chan_bool(true));
    row->ring[(row->head + row->size) % row->room] = item;
    row->size += 1;
  }
  return v;
}

static void chan_free(IoHand h, ChanRow* row) {
  free(row->ring);
  free(row);
  io_sys_kill(h);
}

static void chan_shut(Env e, IoHand h, ChanRow* row) {
  row->shut = 1;
  while (row->wait != NULL) {
    bool rcv = row->wait->item == TERM_HOLE;
    Term x = rcv ? term_pak(CID_NONE, 0) : chan_bool(false);
    term_sink(e, chan_wake(row, x));
  }
  if (row->size == 0) {
    chan_free(h, row);
  }
}
