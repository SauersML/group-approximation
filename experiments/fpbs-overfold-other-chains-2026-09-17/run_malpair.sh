#!/bin/sh
# Doubly malnormal nested pairs (A and B both malnormal in F): hunt for deep < law.
cd "$(dirname "$0")"
{
python3 malpair.py 3000 1 11 4 3 2 5 3
python3 malpair.py 3000 1 12 4 3 3 5 3
python3 malpair.py 2000 1 13 4 3 2 6 4
python3 malpair.py 1000 1 14 4 4 3 5 3
python3 malpair.py 500 2 15 4 3 2 5 3
python3 malpair.py 300 3 16 4 3 2 5 3
# equal ranks rk A = rk B = 3
python3 malpair.py 400 2 21 4 3 3 5 3
python3 malpair.py 200 3 22 4 3 3 5 3
python3 malpair.py 2000 1 23 4 3 3 6 5
} > malpair.txt
python3 verify_gaps.py malpair.txt > malpair_verify.txt
