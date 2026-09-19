#!/bin/sh
# Completes run_named.sh (whose n = 5 loop stopped at psi_baBB_j2).
cd "$(dirname "$0")"
{
python3 chains.py psi_baBB_j2 5 10 1 4
for c in psi_baBaB_j1 psi_bbaBBB_j1 psi_baabBB_j1 psi_bAbaBB_j1 psi_baBaaB_j1; do
  python3 chains.py $c 5 40 1 4
done
python3 chains.py psi_baabBB_j1 6 20 2 4
} > named_n5b.txt
