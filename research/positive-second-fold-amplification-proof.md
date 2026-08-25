---
rg: 2
id: positive-second-fold-amplification-proof
kind: route
title: Take slowly growing tensor powers of any fold-square outlier
target: positive-second-fold-bias-amplifies-to-full-rigidity
requires:
  - congruence-tensor-regularizes-sl3-swap-profile
---

Profile regularization identifies the regular/balanced positive-bias claim
with a uniform positive lower bound for arbitrary assignments.  If full
rigidity fails, pass to a sequence with real second-fold trace at most
`1-c`.  A nonpositive subsequence already violates the lower bound.  On a
positive subsequence, take tensor powers `k_n->infinity` slowly enough that
`k_n delta_n->0`.  Relator defects grow by at most `k_n`, while the
second-fold trace becomes at most `(1-c)^(k_n)->0`, again violating the
lower bound.
