#!/bin/sh
# Mid-n relative (O) census queue (see research/artifacts/fpbs-overfold-midn-exact-2026-09-20.md).
cd "$(dirname "$0")"
python3 midn.py 2 12 40 212 3 3600 - 2 > rand_j2_n12.txt 2>&1
python3 struct_midn.py psl 23 30 23 1 4 7200 5 2 > psl23_j1_law5.txt 2>&1
# same 30 levels (same seed); only the law-6 ones, s <= 3
python3 struct_midn.py psl 23 30 23 1 3 7200 6 2 > psl23_j1_law6_s3.txt 2>&1
