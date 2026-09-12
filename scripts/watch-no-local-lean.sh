#!/bin/sh

# Keep this workstation free of local Lean/Lake compilation.  Exact process
# names avoid matching editors, Codex/Claude agents, or unrelated shell text.
while :; do
  pkill -TERM -x lean 2>/dev/null || true
  pkill -TERM -x lake 2>/dev/null || true
  sleep 1
done
