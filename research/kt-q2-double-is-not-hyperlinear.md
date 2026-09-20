---
rg: 2
id: kt-q2-double-is-not-hyperlinear
kind: claim
title: "Every q=2 Kun-Thom double with r,d>=3 is not hyperlinear"
distinct_from:
  kun-thom-lamp-wreath-is-not-hyperlinear: "That concerns the ordinary binary coset wreath and its marked lamp collapse; this concerns the symmetric amalgamated group double, transferred through the established equivalence."
  kt-wreath-hyperlinear-iff-double-hyperlinear: "That equates hyperlinearity of several objects without deciding it; this asserts the negative answer for every q=2 Theorem E double with r,d>=3."
  kt-pair-group-double-is-nonsofic: "That excludes permutation approximations for the family of doubles; this excludes normalized Hilbert-Schmidt approximations for its entire q=2 subfamily."
artifacts:
  - research/artifacts/liu-internality-normalization-audit-2026-09-20.md
---

## Attribution

The analytic input is Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Theorem 1.2 / 6.7, followed by Theorem 1.3 / 7.4.
The conditional normalization/double construction is due to Andreas Thom,
[*A conditional construction of a nonhyperlinear group and the centralizer problem*](https://andreasthom.github.io/pdf/nonhyperlinear.pdf),
Theorems 1.2-1.3; the pairs and lamp construction are due to Gabor Kun and
Andreas Thom, [*Nonsofic wreath products of residually finite groups*](https://arxiv.org/abs/2608.06222),
Theorems A and E. This family-wide conclusion is a downstream application
through the named prerequisites, not a verbatim import of Liu's
fixed-parameter Theorem 8.3.

For every pair of integers `r,d>=3`, fix `q=2` and set

```text
Gamma=EL_r(F_2[x_1,...,x_d]),
G=EL_r(F_2[x_1^(+-1),...,x_d^(+-1)]) rtimes SL_d(Z),
D=G *_Gamma G.
```

The claim is that `D` is not hyperlinear: no injective homomorphism from
`D` into the unitary group of a tracial matrix ultraproduct exists.
The subgroup embeddings in the amalgam are the two copies of the displayed
polynomial inclusion. The claim quantifies over all `r,d>=3` with `q=2`.

## Attempts

2026-09-20: the route through
`kt-wreath-hyperlinear-iff-double-hyperlinear` transfers the corresponding
binary-wreath family obstruction for every `r,d>=3`. The wreath conclusion remains conditional on
the separately recorded analytic/normalization chain. Thom's conditional
double construction is consistent with this route but is not imported here
as an unconditional theorem.
