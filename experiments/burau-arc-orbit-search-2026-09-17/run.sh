#!/bin/sh
# Reproduce the exhaustive n=4 Bigelow arc-pair search (M=250) and its controls.
# Single-threaded; each shard is one top-level start (free-puncture side, height order, q2 side).
set -e
cd "$(dirname "$0")"
gcc -O2 -o arcfast2 arcfast2.c
gcc -O2 -o arcpairs_np arcpairs_np.c
mkdir -p runs
# controls
./arcfast2 4 14 1 > runs/ctl_arcfast2_n4_M14_noprune.txt
NOPRUNE=1 ./arcpairs_np 4 2 12 > runs/ctl_arcpairs_n4_m12_noprune.txt
./arcfast2 6 8 1 > runs/ctl_arcfast2_n6_M8_noprune.txt
NOPRUNE=1 ./arcpairs_np 6 8 8 > runs/ctl_arcpairs_n6_m8_noprune.txt
./arcfast2 3 80 0 > runs/ctl_arcfast2_n3_M80.txt
# main run: 28 top-level starts for n=4
for s in $(seq 0 27); do
  ./arcfast2 4 250 0 5 $s $((s+1)) > runs/n4_M250_s$s.txt
done
cat runs/n4_M250_s*.txt | grep -c "total_hits=0"   # expect 28
