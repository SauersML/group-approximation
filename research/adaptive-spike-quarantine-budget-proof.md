---
rg: 2
id: adaptive-spike-quarantine-budget-proof
kind: route
title: Give the nth encountered spike a geometric trace allowance
target: adaptive-spike-quarantines-have-summable-trace
requires:
  - low-gap-witness-spike-or-balanced-cut
  - small-trace-rank-one-quarantine
---

At the `n`th active corner choose `C_n` by `(ASQ2)`.  The clipping lemma's
relative trace estimate becomes the global estimate
`tau(r_n)<=eta 2^(-n)`.  Removing a spike before continuing makes the
supports disjoint.  Geometric summation proves `(ASQ1)`, and the rank-one
quarantine lemma charges its refinement linearly in the same total trace.
