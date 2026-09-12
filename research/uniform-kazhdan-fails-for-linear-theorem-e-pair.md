---
rg: 2
id: uniform-kazhdan-fails-for-linear-theorem-e-pair
kind: claim
title: The Kun--Thom Theorem E pair is linear, so it has no uniform Kazhdan constant
distinct_from:
  hs-normalization-profile-rounding-crux: that is the finite-stage rounding lemma whose error may depend on a fixed generating set; this records that the generating set cannot be quantified away, because the group is linear and uniform property (T) fails for it.
  invariant-size-collapse: that is an algebraic collapse principle with no quantitative constant; this is a citation fact about Kazhdan constants across generating sets for linear groups.
artifacts:
  - research/artifacts/rigid-compression-defect-ladder-2026-09-11.md
---

**ESTABLISHED by citation.** Lubotzky--Yao, *Non Uniform Kazhdan Constant for
Linear Groups*, arXiv:2608.03561v2 (31 Aug 2026), abstract:

> `SL_n(Z)`, `n >= 3`, is not uniformly (T). Moreover, the same holds for
> every infinite finitely generated linear group.

The Kun--Thom Theorem E pair `Gamma = EL_r(F_q[x_1,...,x_d])`,
`G = EL_r(F_q[x^(+-1)]) semidirect SL_d(Z)` (`r, d >= 3`) is linear over a
field, and both members are infinite and finitely generated. So neither has a
Kazhdan constant bounded below over all finite generating sets.

**Consequence for the Hilbert--Schmidt normalization program.** Any proof of
`hs-normalization-profile-rounding-crux`, or of
`kt-centralizer-normalization-hs` through it, may use the gap `kappa` only at a
single fixed generating set. A rounding or concentration bound whose constant
degrades as the generating set is enlarged -- for instance one that passes to
words in a growing alphabet, or that quantifies over all Kazhdan pairs in the
compression semigroup with their own generating sets -- cannot be invoked for
this instance. This does not obstruct the fixed-generating-set form used in the
crux lemma; it fences the space of admissible arguments.

**Trust surface.** External preprint, read at abstract level on 2026-09-12 by
the literature scout; the two quoted sentences are the source abstract. No proof
step is imported.

DERIVATION
uniform-kazhdan-fails-for-linear-theorem-e-pair-citation
