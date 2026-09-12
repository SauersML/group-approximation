---
rg: 2
id: nonhyperlinear-from-source-specific-rank-router-face
kind: route
title: Use one pointed independent-set source face instead of a universal tensor-closed router
target: non-hyperlinear-group
requires:
  - fixed-nonru-independent-set-orthogonality-game-exists
  - outcome-count-free-subpovm-completion
  - independent-finite-clocks-round-to-arbitrary-row-pvms
  - rank-conjugacy-detects-projection-overlap
  - source-specific-pointed-rank-router-face
artifacts:
  - research/artifacts/hybrid-rank-router-tensor-closure-2026-08-23.md
---

The pointed source face supplies exactly the routing conclusions used in
the former hybrid-router terminal, but only for canonical matrix
microstates and the one distinguished perfect tracial source.  This is all
the nonhyperlinearity argument needs.

On a separated marked corner, row rounding produces one finite-dimensional
independent-set strategy.  Rank conjugacy and `(SPR1)` give

```text
E_rel >= c (sum_f alpha_f ||P_fQ_f||_2^2)^2-o(1).       (SPR2)
```

The fixed independent-set gap makes the right side uniformly positive,
contradicting vanishing canonical microstate defect.  One-source
completeness supplies an exact tracial representation with nonzero mark, so
the marked group word is nontrivial.  Hence a hyperlinear canonical trace is
impossible and the resulting group is nonhyperlinear.

Tensor closure causes no contradiction because the premise
`source-specific-pointed-rank-router-face` never asserts that arbitrary
zero-overlap scalar interfaces extend, and its pointed moment face is
explicitly not closed under the tensor construction `(HRT1)`.
