#!/bin/sh
# Random nested-pair hunt, rank-3 B at Q = point; output lands in this directory.
# (Rank-2 runs at n = 3, 4 were too slow in this form and were stopped; the
# rank-2 controls are run_malpair2.sh and run_ri.sh.)
cd "$(dirname "$0")"
python3 randchains.py 400 1 1 34 4 3 3 5 3 0 > rand_r3_n1.txt
