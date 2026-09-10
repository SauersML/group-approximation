---
rg: 2
id: fpbs-pulled-back-graphing-isoperimetry
kind: claim
title: A pulled-back bounded-degree graphing has the same symmetric-vertex isoperimetric constant
artifacts:
  - research/artifacts/fpbs/docs/isoperimetric-test-descent.md
---

For an equivariant pmp factor pi:Y->X of essentially free actions
of a countably infinite group, with ergodic base X, and a fixed
bounded-degree graphing K generating R_X, the symmetric-vertex
isoperimetric constants satisfy h_(K^pi)(R_Y)=h_K(R_X).
Source tests may use arbitrary full-group maps on Y. The proof
constructs base tests by averaging finite-set kernels, separating
their roots, and repairing them into disjoint full-group maps.

Consequently the infimum over pulled-back generating graphings
equals 2(C(R_X)-1). This does not identify it with the infimum
over all source graphings, which is the missing comparison.

Status records a written deduction using a published approximate
edge-coloring theorem, not independent mathematical or Lean
verification. No novelty claim or universal cost equality is made.
