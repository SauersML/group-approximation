---
rg: 2
id: atlas-m3-permutation-gauge-joint-no-go-proof
kind: route
title: Replay the universal binary packet frame over all S6 gauges
target: atlas-m3-permutation-gauge-joint-no-go
requires:
  - atlas-repeated-h6-gauge-is-one-gl2m-coordinate
  - atlas-shortest-a4-triangle-packet
  - atlas-word-19243-is-kernel-relation
  - atlas-q14-adds-stratified-thirteenth-double-coset
artifacts:
  - experiments/atlas_a4_m3_permutation_gauge_ansatz.py
  - experiments/atlas-a4-m3-permutation-gauge-ansatz.json
---

The script forms `U=C(T)(U0 tensor I_3)` for each of the 720 permutation
matrices `T`.  It tests all H18 cross cubes after the H6-central gauge, then
evaluates both stored kernel words by literal `12 x 12` binary multiplication.
Exact Sage arithmetic and the pinned artifact give the counts and `(M3P2)`
without sampling.
