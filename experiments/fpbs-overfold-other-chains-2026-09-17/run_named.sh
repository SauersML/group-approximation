#!/bin/sh
# Named chains of chains.py: 40 random transitive Q with n = 5, 20 with n = 6.
cd "$(dirname "$0")"
: > named_n5.txt
: > named_n6.txt
for c in mal1 Lt_tatT Lt_tt Lt_tatt Lt_ttaT Bab_x psi_baBB_j1 psi_baBB_j2 \
         psi_baBaB_j1 psi_bbaBBB_j1 psi_baabBB_j1 psi_bAbaBB_j1 psi_baBaaB_j1; do
  python3 chains.py $c 5 40 1 4 >> named_n5.txt
done &
for c in mal1 Lt_tatT Lt_tt Lt_tatt Bab_x psi_baBaB_j1 psi_baabBB_j1; do
  python3 chains.py $c 6 20 2 4 >> named_n6.txt
done &
wait
