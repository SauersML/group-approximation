---
rg: 2
id: finite-augmentation-partials-are-permutable-transports
kind: claim
title: A literal augmentation compression is a partial isometry exactly for permuting conjugate subgroups
distinct_from:
  finite-character-one-sided-stabilizer-is-its-normalizer: that treats full return on a finite character projection; this classifies proper partial transports of the entire augmentation complement and computes their exact trace loss.
  finite-subgroup-hecke-literals-cannot-block-escape: that classifies literal compressions which are projections; this allows non-self-adjoint partial isometries and identifies the subgroup geometry of their initial and final projections.
artifacts:
  - research/artifacts/finite-augmentation-outside-normalizer-two-context-cell-2026-09-08.md
---

Let `K<=G` be finite of order `k>=2`, let `q=1-e_K`,
and set `L=gKg^(-1)` for `g in G`. Then

```text
qgq is a partial isometry  iff  KL=LK.
```

When this holds, `M=KL` is a finite subgroup. If
`h=|K intersect L|`, the range projection and canonical trace
loss are

```text
(qgq)(qgq)^*=1-e_K-e_L+e_M,
tau(q-(qgq)(qgq)^*)=(k-h)/k^2.
```

For `g` outside `N_G(K)`, this loss is at least `1/(2k)`,
or at least `1/(2(k-1))` of the corner trace. A full corner
unitary occurs exactly when `g` normalizes `K`.

DERIVATION
finite-augmentation-subgroup-average-partial-proof
