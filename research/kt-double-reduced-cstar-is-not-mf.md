---
rg: 2
id: kt-double-reduced-cstar-is-not-mf
kind: claim
title: "Every q=2 Kun-Thom double with r,d>=3 has non-MF reduced C-star algebra"
distinct_from:
  kt-double-reduced-cstar-is-mf: "That seeks a norm-corona embedding for the q=2 double; this excludes such an embedding for every parameter choice r,d>=3 in that same family."
  kt-q2-double-is-not-hyperlinear: "That excludes injective tracial matrix-ultraproduct group models; this excludes a norm-matrix-corona embedding of the reduced C-star algebra, using its unique trace."
  kt-full-double-cstar-is-not-mf: "That concerns the full group C-star algebra and its proper-isometry obstruction; this concerns the reduced algebra, where that full-algebra obstruction does not directly apply."
artifacts:
  - research/artifacts/liu-internality-normalization-audit-2026-09-20.md
---

## Attribution

The analytic input behind the negative group prerequisite is Jihao Liu,
[*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Theorem 1.2 / 6.7 and Theorem 1.3 / 7.4. Andreas Thom's
[Theorems 1.2-1.3](https://andreasthom.github.io/pdf/nonhyperlinear.pdf)
supply the conditional normalization/double construction; Gabor Kun and
Andreas Thom's [Theorems A and E](https://arxiv.org/abs/2608.06222)
supply the pair and lamp construction. This reduced-C-star consequence
uses the named unique-trace input as well. It is a downstream corollary,
not a statement quoted from Liu's fixed-parameter Theorem 8.3.

For every pair of integers `r,d>=3`, let `D=G *_Gamma G` be the `q=2`
double at those parameters defined in `kt-q2-double-is-not-hyperlinear`.
The reduced group C-star algebra
`C*_r(D)` is not MF: it admits no faithful star-homomorphism into a matrix
norm corona `product_n M_(k_n)/direct_sum_n M_(k_n)`.

This is a statement about the reduced C-star algebra, not a negation of
abstract-group weak MF or of MF for a different completion of the group
algebra. The matrix norm and normalized Hilbert-Schmidt norm are distinct;
the unique reduced trace is the bridge used by the proof.

## Attempts

2026-09-20: combine the conditional negative double conclusion with the
established unique reduced trace. Any norm-corona embedding would induce
the canonical trace in a tracial matrix ultraproduct and hence a faithful
group model. The attempted positive reduced-MF construction is thereby
excluded only once the negative double prerequisite is established. No
general permanence obstruction or conclusion for `q!=2` is asserted.
