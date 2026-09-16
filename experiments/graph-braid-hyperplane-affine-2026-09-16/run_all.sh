#!/bin/sh
# Replays every case quoted in the 2026-09-16 artifact and notes, exactly over Q.
# Single-threaded; each run capped at 10 minutes. Output: results-2026-09-16.txt
cd "$(dirname "$0")"
out=results-2026-09-16.txt
: > "$out"
for args in "K4 2 1" "K4 2 2" "K4 2 3" "K4 2 1,2,1,3,1,2" \
            "theta 2 2" "theta 2 3" "theta 2 4" "theta 2 2,2,3" "theta 2 1,2,2" "theta 2 1,3,3" \
            "theta4 2 2" "K5 2 1" "K33 2 1" "cycle3 2 2" "figure8 2 2" "dumbbell 2 2" \
            "triangle_with_legs 2 2" "lollipop 2 2" "triod 2 2" "star4 2 2" "Htree 2 2" \
            "theta 3 3" "K4 3 2" "cycle3 3 3" "lollipop 3 3" "triod 3 3" "star4 3 3" "Htree 3 3" \
            "K4_triangle 2 2" "K4_bridge_cycle 2 2"; do
  EXACT=1 timeout 600 python3 hyperplane_affine.py $args >> "$out" 2>&1 || echo "FAILED/TIMEOUT: $args" >> "$out"
done
