---
rg: 2
id: wave4-visibility-filtered-elimination-proof
kind: route
title: Invert the linear two-face Jacobian and prove filtration contraction and mutually inverse evaluation maps
target: wave4-visibility-marked-lie-four-generator-elimination
requires:
  - wave4-visibility-k7-marked-face-presentation
artifacts:
  - research/artifacts/hyperbolic-rf-wave4-filtered-elimination-2026-09-20.md
  - experiments/hrf-wave4-four-generator-2026-09-20/eliminate.py
  - experiments/hrf-wave4-four-generator-2026-09-20/class_4.json
  - experiments/hrf-wave4-four-generator-2026-09-20/class_5.json
  - experiments/hrf-wave4-four-generator-2026-09-20/class_6.json
---

The linear parts of E,F in U2,V2 have coefficient matrix
[[1,-3/2],[2,-4]], whose inverse is [[4,-3/2],[2,-1]]. Its
constant-Jacobian correction kills the current residual to one
higher filtration degree. The initial residual has degree at least
two, so C-1 iterations suffice. The same contraction argument makes
solutions unique in every class-C target Lie algebra.

Inclusion of the first four generators and evaluation at the
unique solution are inverse maps between freeLie4 and the
six-generator quotient by E,F. All remaining relations, including
the exact canonical mark, transport under this isomorphism.

The artifact gives the full proof and exact-arithmetic implementation.
Completed ideal closures and marked reductions are in the three
JSON receipts; class4 and class5 also match the independently run
six-generator implementation.
