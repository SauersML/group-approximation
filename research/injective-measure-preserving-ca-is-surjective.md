---
rg: 2
id: injective-measure-preserving-ca-is-surjective
kind: claim
title: An injective cellular automaton preserving the uniform Bernoulli measure is surjective
distinct_from:
  strict-automaton-lowers-bernoulli-rokhlin-entropy: that measures the non-surjectivity defect quantitatively as a drop in Bernoulli Rokhlin entropy; this is the elementary qualitative endpoint using only full support of the uniform measure and closedness of the image.
  surjunctivity-passes-to-subgroups: that is heredity of surjunctivity along subgroup inclusions; this is a measure-theoretic sufficient condition for one automaton to be surjective.
  gottschalk-surjunctivity-conjecture: that asserts every injective automaton over every group is surjective; this reduces surjectivity of one injective automaton to preservation of the uniform Bernoulli measure.
artifacts:
  - research/artifacts/gottschalk-kazhdan-direct-attack-2026-09-12.md
---

ESTABLISHED. Let `G` be a countable group, `A` a finite alphabet, and `mu_A` the
uniform Bernoulli measure on `A^G` (the product of the uniform measure on `A`),
which has full support. If an injective cellular automaton `tau: A^G -> A^G`
preserves `mu_A`, that is `tau_* mu_A = mu_A`, then `tau` is surjective.

Proof. `A^G` is compact and `tau` continuous, so `Y = tau(A^G)` is closed. Then
`tau^{-1} Y = A^G`, so `mu_A(Y) = tau_* mu_A(Y) = 1`. The complement is open and
`mu_A`-null, and `mu_A` has full support, so the complement is empty and
`Y = A^G`.

Consequence. For any group, surjunctivity follows once every injective cellular
automaton preserves `mu_A`, and a strict injective automaton is exactly a
measure-distorting one (its image is a proper closed set, of measure below one by
full support). So the positive surjunctivity question over a fixed group is
exactly whether injectivity forces preservation of the uniform Bernoulli measure.
This is the elementary qualitative form of the quantitative Rokhlin-entropy route.
