---
rg: 2
id: fp-torsion-free-nonhyperlinear-group-of-cd-at-most-three
kind: claim
title: "A finitely presented torsion-free nonhyperlinear group has cohomological dimension at most three"
distinct_from:
  fp-torsion-free-nonsofic-group-of-cd-at-most-three: "That asserts nonsoficity; this proves the strictly stronger nonhyperlinearity obstruction using Liu–Thom normalization, without importing an exact dimension lower bound."
artifacts:
  - research/artifacts/torsion-free-nonhyperlinear-rips-double-2026-09-20.md
---

There exists a finitely presented torsion-free group P which is not
hyperlinear and satisfies `cd_Z(P)<=3`.

One witness is the double `P=G *_H G`, where G is the Ollivier–Wise
torsion-free graphical Rips cover of `L_(F_2)(1,2)^x` and H is the
preimage of the native four-by-four strict Kazhdan compression
subgroup diag(EL_3(R),1). The cover has `cd_Z(G)<=2`; H is finitely generated,
which suffices for finite presentation of the double. No exact
dimension-three assertion is included.

This is a downstream consequence of Jihao Liu,
[*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf),
Theorem 1.2 / 6.7, and Andreas Thom's
[*A conditional construction of a nonhyperlinear group and the centralizer problem*](https://andreasthom.github.io/pdf/nonhyperlinear.pdf),
Theorems 1.2–1.3, through the credited all-trace normalization and
double obstruction. The cover is due to Yann Ollivier and Daniel T.
Wise, [Theorem 1.1 and Section 2.1](https://arxiv.org/pdf/math/0409203v1).
The artifact and proof route retain the existing Leavitt algebra and
finite-presentation inputs explicitly. No independent analytic
discovery or novelty claim is made.

The same witness satisfies Baum–Connes with coefficients, by
`fp-torsion-free-nonhyperlinear-bcc-group-exists`. The assembly proof is
independent of the nonhyperlinearity input. Thus this double is excluded
as a candidate for the ordinary Baum–Connes counterexample root.
