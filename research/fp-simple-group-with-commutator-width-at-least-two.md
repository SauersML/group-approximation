---
rg: 2
id: fp-simple-group-with-commutator-width-at-least-two
kind: claim
title: Some finitely presented simple group has commutator width at least 2
distinct_from:
  fp-infinite-simple-group-not-two-generated: that asks for a finitely presented simple group of generating rank at least 3; this asks for one in which some element is not a single commutator.
  nikolov-segal-uniform-commutator-width: that is about finite groups and profinite completions; this is about infinite finitely presented simple groups.
artifacts:
  - research/artifacts/gq-bh-openq-lists.md
---

**ANSWERED IN THE LITERATURE (yes), before the AIM list recorded it.** Caprace and
Fujiwara, *Rank one isometries of buildings and quasi-morphisms of Kac–Moody groups*
(GAFA 20 (2010); arXiv:0809.0470, TeX read on MSI, sha256 ae6ae1e6…c07879), prove:
- Corollary `cor:KM:CommutatorWidth` (TeX l.262–267): for a Kac–Moody–Tits functor 𝒢 whose
  Weyl group is irreducible, non-spherical and non-affine, and any integral domain R, the
  space of homogeneous quasimorphisms of 𝒢(R) is infinite-dimensional, so 𝒢(R) has
  elements of positive stable commutator length and infinite commutator width.
- Corollary `cor:KM:simple` (TeX l.292–295): "There exists an infinite family of pairwise
  non-isomorphic finitely presented simple groups possessing elements of strictly positive
  stable commutator length; these groups have therefore infinite commutator width." The
  simplicity and finite presentation come from Caprace–Rémy (2-spherical Weyl group, finite
  field of order larger than the rank). The authors present this as answering Bardakov's
  Kourovka Problem 14.13.

So the third item of AimPL Problem 3.1 has answer **yes**, with commutator width infinite.
No proof on main is needed and no priority is ours: this node records a status correction
(bh-free-60, 09-18). The first two items of Problem 3.1 (ρ_1, ρ_2 for F, T, V and
topological full groups) are unaffected.

**Original record (kept).** Printed in the AIM problem list *Groups of dynamical origin*
(http://aimpl.org/groupdynamorigin, section 3 "Thompson groups", Problem 3.1, accessed
2026-09-18). With `ρ_1(g)` the commutator width of `g` and `ρ_2(g)` the least number of
involutions in a factorization of `g`, for `G` one of `F, T, V` or a topological full
group, the problem asks:

> Prove that ρ_1 and ρ_2 are bounded. Prove that ρ_1 = 1 and ρ_2 = 3. Is there a
> finitely presented simple group with commutator width greater or equal to 2?

This node records the third item.

**Why it sits next to Boone–Higman.** Commutator width is not inherited by subgroups.
So Boone–Higman embeddings say nothing about it directly, but the question tests whether
finitely presented simple groups share a uniform word-theoretic property.
- The natural lever is standard: a group with a nontrivial homogeneous quasimorphism has
  unbounded commutator length, by Bavard duality. So a finitely presented simple group
  with such a quasimorphism would give a strong yes, with infinite commutator width.
- Candidate sources are finitely presented simple groups with WPD actions on hyperbolic
  spaces (Bestvina–Fujiwara). (Superseded: Caprace–Fujiwara use rank-one isometries of a
  single twin-building half, which is exactly such a source.)
- Muranov's finitely generated simple groups of infinite commutator width are not known
  to be finitely presented. (Superseded by Caprace–Fujiwara Cor `cor:KM:simple`.)

**Tractability (original, superseded).** Medium. A quasimorphism on any explicit finitely
presented simple host used on main would answer it; so would an explicit element of
length 2 in a twisted Brin–Thompson group.
