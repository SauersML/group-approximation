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

**OPEN.** Printed in the AIM problem list *Groups of dynamical origin*
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
  spaces (Bestvina–Fujiwara). No finitely presented simple group with that property is
  known to this lane.
- Muranov's finitely generated simple groups of infinite commutator width are not known
  to be finitely presented.

**Tractability.** Medium. A quasimorphism on any explicit finitely presented simple host
used on main would answer it; so would an explicit element of length 2 in a
twisted Brin–Thompson group.
