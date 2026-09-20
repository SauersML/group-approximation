---
rg: 2
id: kt-q2-double-nonhyperlinear-from-wreath
kind: route
title: "Transfer the binary wreath family obstruction to every q=2 symmetric double"
target: kt-q2-double-is-not-hyperlinear
requires:
  - kun-thom-wreath-family-is-not-hyperlinear
  - kt-wreath-hyperlinear-iff-double-hyperlinear
---

## Attribution

The analytic input to the family prerequisite is Jihao Liu,
[*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Theorem 1.2 / 6.7 and Theorem 1.3 / 7.4. The conditional
normalization/double construction is due to Andreas Thom,
[Theorems 1.2-1.3](https://andreasthom.github.io/pdf/nonhyperlinear.pdf),
and the pairs and lamp construction to Gabor Kun and Andreas Thom,
[Theorems A and E](https://arxiv.org/abs/2608.06222). This is a downstream
corollary for the q=2 family, not an expansion of the statement of Liu's
fixed-parameter Theorem 8.3.

Fix any integers `r,d>=3`. Specialize the equivalence prerequisite to `q=2`
and these same `r,d`, with the
polynomial subgroup, Laurent actor, and left-coset action in the target.
Its ordinary binary wreath is the corresponding member of
`kun-thom-wreath-family-is-not-hyperlinear`. If the double `G *_Gamma G`
were hyperlinear, the equivalence would make that wreath hyperlinear,
contradicting the first prerequisite. Therefore this double is not
hyperlinear. Since `r,d` were arbitrary, this proves the entire q=2
subfamily; every application of the equivalence matches parameters.
