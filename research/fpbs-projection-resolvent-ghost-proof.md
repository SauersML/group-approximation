---
rg: 2
id: fpbs-projection-resolvent-ghost-proof
kind: route
title: Scale edge and ghost odds together and calculate the two-vertex obstruction
target: fpbs-projection-resolvent-ghost-obstruction
requires:
  - fpbs-projection-noise-variance-identity
  - fpbs-bernoulli-projection-resolvent-bound
artifacts:
  - research/artifacts/fpbs/projection-resolvent.md
---

Section 4 repeats the product-coordinate variance proof for nested
constraint-kernel projections with activation odds t w_i. It derives
-tQ_t'>=Q_t-Q_t^2, integrates the inverse inequality, and exhausts the
constraints. The explicit two-by-two matrices refute the subtraction
inequality on a diagonal test vector. No refutation of the original
critical L2 conjecture or percolation goal is claimed.
