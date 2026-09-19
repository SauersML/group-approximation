---
rg: 2
id: finite-game-gap-makes-the-cyclic-acceptance-compressor-strict
kind: claim
title: A finite game gap makes the cyclic product of all acceptance projections a strict contraction
distinct_from:
  one-product-of-verifier-reflections-does-not-control-game-energy: that shows phase cancellation for a unitary product of reflections; this uses positive acceptance compressions.
  one-gram-vector-decodes-a-finite-bcs-strategy: that lower-bounds the sum of rejection energies; this packages the gap into one sequential return.
  fanizza-heat-filter-has-uniform-cstar-decay: that uses an infinite functional-calculus family; this uses one finite product.
---

If projections `L_1,...,L_m` satisfy

```text
sum_j alpha_j ||L_j xi||^2 >= lambda ||xi||^2
```

with all `alpha_j>0`, then for `Q_j=I-L_j` and
`T=Q_m...Q_1`,

```text
||T||_op^2 <= 1-lambda/[alpha_max m(m+1)/2] < 1.
```

Hence the cyclic acceptance compressor of any fixed finite game with a
strict finite-dimensional gap has a dimension-independent contraction gap.
For BCS Gram space this product is one fixed finite Hecke bimodule
coefficient.  The remaining groupification problem is to return a
positive-density marked Gram block through that coefficient; the analytic
contraction itself is complete.
