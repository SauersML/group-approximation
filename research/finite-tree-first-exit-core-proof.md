---
rg: 2
id: finite-tree-first-exit-core-proof
kind: route
title: Balance ranks, intersect pulled-back polar sources, and propagate the common core
target: finite-tree-first-exits-extract-an-equal-rank-global-pvm
requires:
  - polar-compression-turns-band-mismatch-into-first-exit
  - equal-rank-denominator-edges-authenticate-decoded-atoms
---

Two-sided leakage gives the exact rank-difference identity `(TFE7)`, so
trimming every vertex to the minimum tree rank costs at most a fixed
multiple of total leakage.  Polar-compress each equal-rank tree edge.  Pull
the source projection of every path back to the root and intersect the
finitely many results; the trace union bound charges only the sum of missing
sources.  Transport this intersection along unique tree paths.  The images
have equal rank, lie in the original chart atoms, and are exactly related by
the polar tree transitions.  Raw transition leakage and every non-tree
covariance are then bounded by the polar displacement plus the trace of the
trimmed complements.

