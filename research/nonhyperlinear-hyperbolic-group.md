---
rg: 2
id: nonhyperlinear-hyperbolic-group
kind: claim
title: A word-hyperbolic group is not hyperlinear
root: true
distinct_from:
  nonsofic-hyperbolic-group: That only excludes permutation approximation; this excludes unitary Hilbert--Schmidt approximation and implies that target.
  non-hyperlinear-group: That general existence target is established using Liu; this imposes word hyperbolicity, which the known witnesses do not acquire.
  kazhdan-hyperbolic-hs-stability-kills-hyperlinearity: That is a conditional construction theorem; this asks for an actual witness satisfying its input or another construction.
artifacts:
  - research/artifacts/liu-new-frontiers-2026-09-20.md
---

OPEN. Exhibit a word-hyperbolic group with no faithful tracial
matrix-ultraproduct model. This would also give a nonsofic and
non-residually-finite hyperbolic group. It does not follow from the
nonhyperlinear quotient of a hyperbolic Rips cover.

## Attempts

2026-09-20: applying Jihao Liu's internality theorem to the existing
compression witnesses does not solve the transport problem. The
repository theorem `hyperbolic-local-embedding-kills-compression-certificates`
rules out both embedding these witnesses and realizing them as marked
limits of subgroups of hyperbolic groups. This is stronger than an
unproved transfer lemma: the unchanged certificate cannot survive.
The torsion-free double of cohomological dimension at most three is
not proved hyperbolic.

A separate surviving route is flexible HS stability of a Kazhdan
hyperbolic group with positive second Betti number, through the existing
Dogon--Vigdorovich finite-central-extension argument. The concrete
`ghb7-flexibly-hs-stable` candidate is still open: its relevant positive
second Betti number belongs to the torsion-free congruence kernel, not
GHB7 itself. Known Kazhdan property does not by itself give this stability.
Start with its recorded
degree-two obstruction, not another attempt to embed a Leavitt group.
