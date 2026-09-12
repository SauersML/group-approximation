---
rg: 2
id: torsion-free-scalar-df-failure-gives-exotic-idempotents-proof
kind: route
title: The product of a one-sided pair in the other order is idempotent, nonzero, and not one
target: torsion-free-scalar-df-failure-gives-exotic-idempotents
requires: []
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/fournier-facio-torsion-free-host-constraints-2026-09-12.md
---

Section 3 of the artifact. `e^2 = alpha (beta alpha) beta = e`. `e != 1` by
hypothesis. `beta e alpha = (beta alpha)^2 = 1` forces `e != 0`, and `e - e^2 = 0`
has both factors nonzero.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 7 of the linear-family verification artifact.*
