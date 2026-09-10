---
rg: 2
id: fpbs-sparse-base-cycle-rounding-proof
kind: route
title: Descend coupled separators and pay their rank before replacing finite pieces by trees
target: fpbs-sparse-base-connected-cycle-rounding
requires:
  - fpbs-sparse-fiid-approximate-hyperfiniteness
  - fpbs-local-equivalence-separator-rounding
  - fpbs-relative-cycle-operator-descent
artifacts:
  - research/artifacts/fpbs/docs/sparse-base-surgery.md
---

Sections 2--4 give the deduction. Join the invariant cut coupling to
the Bernoulli base, normalize on A, and transfer the small separation
number using local equivalence. The transferred cut lives on X.
Finite-component tree replacement preserves every original connection.
For the trace estimate, project ambient cycle chains supported on H[A]
to the cut coordinates: the kernel consists of finite-piece cycles
and the image has dimension at most the cut cost. Rank-nullity bounds
Tr(K) by the deleted tree surplus plus that cost. The relative operator
identity supplies the final source-cost comparison under sparse support.

The artifact also gives a shorter derivation of the separator step
directly from Fraczyk's Theorems 1.9 and 3.10. Separator descent is
already supplied by the cited literature; the connected replacement
and supported-cycle estimate are the deductions recorded here.
