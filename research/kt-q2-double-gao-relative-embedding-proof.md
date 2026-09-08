---
rg: 2
id: kt-q2-double-gao-relative-embedding-proof
kind: route
title: Apply the general tensor-swap relative-embedding equivalence to the Kun--Thom pair
target: kt-q2-double-hyperlinear-iff-relative-embeddable
requires:
  - binary-free-and-ordinary-coset-wreaths-share-hyperlinearity
artifacts:
  - research/artifacts/tensor-swap-expectation-repair-2026-09-07.md
---

Apply the prerequisite to the countable Kun--Thom subgroup inclusion
`Gamma<=G`. It gives hyperlinearity of `G *_Gamma G` if and only if
`L(Gamma)<=L(G)` is relatively embeddable over scalars. The canonical
tracial amalgamated free product satisfies

```text
L(G) *_(L(Gamma)) L(G) = L(G *_Gamma G).
```

Connes embeddability of this algebra is equivalent to hyperlinearity of
the countable group double. Together these give all three conditions.
The proof no longer uses a relative-Haar matrix from the external SLd
quotient or the problematic plain-double square in the printed source.
