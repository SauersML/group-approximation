#!/bin/bash
# Exact width-degree grid Lambda_S(D, L) for a monomial set S in the positive monoid of F.
# Reuses the min-cut + Dinkelbach solver experiments/thompson-f/doubling_flow.cpp (unchanged).
#
# usage (from the repository root):
#   g++ -O2 -std=c++17 -o /tmp/dflow experiments/thompson-f/doubling_flow.cpp
#   bash experiments/thompson-f-2026-09-17/width_degree_grid.sh /tmp/dflow "<monomials>" DMAX LMAX > grid.txt
#   python3 experiments/thompson-f-2026-09-17/width_degree_law.py s35 grid.txt
#
# monomials: normal forms separated by ';', letters by ','.
#   X_2     = "0;1;2"
#   S_(2,4) = "0,0;0,1;0,2;1,1;1,2"
#   S_(3,5) = "0,0;0,1;0,2;0,3;1,1;1,2;1,3;2,2;2,3"
# Output lines: "D L <json>".  Cost: S_(3,5) with DMAX=9, LMAX=10 takes a few minutes;
# single points at large L (D=10, L=13: 155 s) were run separately (width_degree_s35_D10_scan.txt).
B="$1"
S="$2"
for D in $(seq 1 "$3"); do
  for L in $(seq 1 "$4"); do
    echo -n "$D $L "
    "$B" "$D" "$L" "$S"
  done
done
