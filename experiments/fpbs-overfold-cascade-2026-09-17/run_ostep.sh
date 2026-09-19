#!/bin/sh
# One-step yield runs.
D=$(dirname "$0")
O=$D/ostep_results.txt
: > $O
cd $D
python3 ostep.py model_j1.txt 100000 3 0 3000 31 >> ostep_results.txt
python3 ostep.py model_j1.txt 100000 4 0 2000 41 >> ostep_results.txt
python3 ostep.py model_j1.txt 100000 4 1 2000 42 >> ostep_results.txt
python3 ostep.py model_j1.txt 12 4 20 300 43 >> ostep_results.txt
python3 ostep.py model_j2.txt 100000 3 0 2000 32 >> ostep_results.txt
python3 ostep.py model_j2.txt 8 3 20 300 33 >> ostep_results.txt
