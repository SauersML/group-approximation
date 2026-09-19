#!/bin/sh
# Control for run_malpair.sh: the same hunt with rk B = 2 (B and A malnormal in F).
cd "$(dirname "$0")"
{
python3 malpair.py 3000 1 41 4 2 2 5 3
python3 malpair.py 3000 1 42 4 2 3 5 3
python3 malpair.py 2000 1 43 4 2 2 6 4
python3 malpair.py 500 2 45 4 2 2 5 3
python3 malpair.py 300 3 46 4 2 2 5 3
python3 malpair.py 400 2 47 4 2 3 5 3
python3 malpair.py 200 3 48 4 2 3 5 3
} > malpair2.txt
