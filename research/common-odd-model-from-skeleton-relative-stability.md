---
rg: 2
id: common-odd-model-from-skeleton-relative-stability
kind: route
title: Levit-Vigdorovich skeletons plus relative gluing produce the common finite odd model
target: approximate-doubling-invariant-joint-measure-is-atomic
requires:
  - skeleton-relative-hs-stability-for-sl2
---

Levit--Vigdorovich HS-stability of `BS(1,4)` (arXiv:2206.02268,
Cor D(3)) exactifies both parabolic skeletons of any accurate
finite-dimensional tuple for `SL_2(Z[1/2])`: each of
`(pi(u), pi(h))` and `(pi(l), pi(h))` is HS-close to an exact
`BS(1,4)` pair whose base has finite odd order, with spectra unions
of `z -> z^4` cycles of odd roots of unity.

`skeleton-relative-hs-stability-for-sl2` then corrects the remaining
gluing data — shared `h`-component, Hoffman--Wielandt alignment of
the two odd spectra for the Weyl swap, and consistency of the Weyl
element as its parabolic word — with dimension-free loss, landing the
whole tuple in one common finite-dimensional model where the
parabolics have a common finite odd order and every coupling word
holds exactly.  That is precisely the target statement, in its
operator (not scalar-measure) form, so the vacuity of the Wasserstein
version is bypassed: eigenvectors, multiplicities and joint moments
are controlled because the model is exact.

Downstream (already wired): on a common odd model, conjugation by
`diag(2, 1/2)` is inner, co-density collapses the commutant by the
mechanism of `odd-congruence-vertex-sector-admits-no-exact-leak`, the
far sector closes through `far-sector-from-doubling-plus-coupling`
into `iwahori-outlier-repair`, and the goal follows through the
Iwahori route.  The two-adic escape structure never activates on odd
skeletons, which is why this route is immune to the plateau evasion
that collapses level-local programs at `SL_3`.
