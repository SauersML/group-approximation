---
rg: 2
id: berend-torus-actions-give-strongly-qd-polycyclic-groups
kind: claim
title: Polycyclic groups Z^3 x| Z^2 from Berend unit actions are strongly quasidiagonal but not virtually nilpotent
distinct_from:
  stw99-eckhardt-wu-decomposition-rank-conjecture: that is the Eckhardt--Wu conjecture equating finite decomposition rank with virtual nilpotence for finitely generated elementary amenable groups; this is the literature fact that makes its forward direction hard, exhibiting non-virtually-nilpotent groups that pass the strong-quasidiagonality test.
artifacts:
  - research/artifacts/stw99-lxxxvi-berend-frontier-2026-08-30.md
---

Let `α` be a root of `t^3 + t^2 − 2t − 1`, let `A ≅ Z^3` be the ring
of integers of `Q(α)`, and let `Σ ≅ Z^2` be the subgroup of the unit
group selected in Eckhardt's proof, acting on `A` by multiplication.  Then
`G = Z^3 ⋊ Σ` is polycyclic, of exponential
growth (it contains a free subsemigroup), not virtually nilpotent, and
`C*(G)` is strongly quasidiagonal.

This is Eckhardt, *A note on strongly quasidiagonal groups*, J. Operator
Theory 73 (2015), arXiv:1309.2205, Theorem 2.4, using Berend's theorem
(Trans. AMS 280 (1983)): every orbit of the unit action on `T^3` is finite
or dense, so every representation of `C*(G) ≅ C(T^3) ⋊ Z^2` is either
faithful on `C(T^3)` — and then, by topological freeness and
Archbold--Spielberg, faithful on `C*(G)`.  Since `G` is amenable and
residually finite, Bekka's theorem makes `C*(G)` residually finite
dimensional, hence its regular representation is quasidiagonal; Voiculescu's
theorem then makes the given faithful essential representation
quasidiagonal.  A representation not faithful on `C(T^3)` instead factors
through a subhomogeneous image.  The last conclusion is the one Eckhardt's
Lemma 2.2 proves; it should not be strengthened to a claim that every
proper quotient is one particular matrix algebra over `C(T^2)`.

The same paper's Theorem 3.3 shows `Z^d ⋊ Z` is strongly quasidiagonal
only when virtually nilpotent.  Thus two commuting automorphisms are
essential to Eckhardt's construction, although the paper does not claim a
global minimality result among all strongly quasidiagonal polycyclic
groups.  By Kirchberg--Winter (finite decomposition rank implies strong
quasidiagonality), the strong-QD obstruction is silent on
`dr(C*(G))`: that is `stw99-lxxxvi-berend-groups-decomposition-rank`.
