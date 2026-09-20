---
rg: 2
id: all-trace-normalization-via-thom-no-drift
kind: route
title: "Thom's conditional no-drift theorem gives normalization from universal internality"
target: kazhdan-compression-pairs-normalize-all-tracial-models
requires:
  - kazhdan-commutants-are-internal
artifacts:
  - research/artifacts/liu-section-six-acceptance-and-thom-bypass-2026-09-20.md
---

## Attribution

This implication is Andreas Thom's
[*A conditional construction of a nonhyperlinear group and the centralizer problem*](https://andreasthom.github.io/pdf/nonhyperlinear.pdf),
Theorem 1.2, with its proof in Sections 2-5. The proposed internality input
is Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Theorem 1.2 / 6.7. Gabor Kun and Andreas Thom's
[Theorems A and E](https://arxiv.org/abs/2608.06222) supply the later
concrete pair and lamp construction. This route credits the conditional
normalization to Thom and does not use Liu's Section 7.

Fix the target's finitely generated Kazhdan pair `Gamma<=G` and an
arbitrary homomorphism `sigma:G->U(M)` into the specified tracial matrix
ultraproduct. If `Gamma=G`, its commutant is fixed pointwise. Otherwise
the subgroup and the chosen compressors generate `G`, so its compression
semigroup generates `G`: every element of `Gamma` is also a compressor.
Thus the pair is infranormal in the sense of Thom's theorem.

The prerequisite applied to `sigma|Gamma` and `sigma` supplies internal
subgroup and ambient commutants. These are precisely the two centralizer
instances used in Thom Proposition 5.1. Relative finite-dimensional
correction aligns their coordinate algebras, and averaging and polar
completion choose compressor lifts commuting with the ambient one.
Thom Theorem 4.2 then applies to the resulting one-sided inclusions and
their common fixed algebra. It upgrades every compressor inclusion to
equality. The subgroup fixes its own commutant pointwise and the
compressors normalize it, so all of `sigma(G)` normalizes it.

The attached acceptance artifact checks the correction, multiplicity,
bounded-scale and conditional-expectation estimates of this deduction.
The printed theorem quantifies over any homomorphism; neither a canonical
trace nor injectivity is required. Stable negligible dimension changes in
the proof are under the common ultraproduct identification, so the final
normalization statement holds in the original `M`.

This is a one-premise conditional route. It does not assert the
prerequisite's unconditional analytic theorem or the stronger statement
that subgroup internality alone suffices in a single model.
