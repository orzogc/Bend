#!/bin/bash
# bench: builds the Bend echo server, its C twin and the load generator
# into /tmp, then runs the load against each (N connections x M round
# trips of 64 bytes). Run from the repo root:
#   bash demos/echo_server/bench.sh
set -e
cd "$(dirname "$0")/../.."
ulimit -n 4096
bun bend2/main.ts demos/echo_server/main.bend -o /tmp/echo_bend
cc -O2 -o /tmp/echo_c demos/echo_server/echo.c
cc -O2 -o /tmp/load demos/echo_server/load.c
run() {
  name=$1
  port=$2
  shift 2
  "$@" > /tmp/$name.out 2>&1 &
  pid=$!
  sleep 0.7
  for cfg in "1 20000" "100 1000" "1000 100"; do
    echo "$name N/M=$cfg: $(/tmp/load 127.0.0.1 $port $cfg 2>&1)"
  done
  kill $pid 2> /dev/null || true
  wait $pid 2> /dev/null || true
}
run bend 7777 /tmp/echo_bend --threads 1
run c 7778 /tmp/echo_c 7778
