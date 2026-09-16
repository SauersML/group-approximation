#!/bin/sh
# Replays the Sigma^1 criterion probe (n = 2) quoted in the artifact's last remark.
# Single-threaded; each run capped at 10 minutes. Output: sigma1-probe-2026-09-16.txt
cd "$(dirname "$0")"
out=sigma1-probe-2026-09-16.txt
: > "$out"
for args in "cycle3 2" "triod 2" "star4 2" "K4 1" "K4 2" "theta 2" "theta 3" "theta 1,2,2" \
            "figure8 2" "lollipop 2" "theta4 2" "triangle_with_legs 2" "dumbbell 2" \
            "K4_triangle 2" "K4_bridge_cycle 2"; do
  timeout 600 python3 sigma1_probe.py $args >> "$out" 2>&1 || echo "FAILED/TIMEOUT: $args" >> "$out"
done
