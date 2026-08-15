---
rg: 2
id: fournier-facio-group-finite-dimensional-shadow
kind: claim
title: Every finite-dimensional representation of the Fournier-Facio group kills the simple factor
distinct_from:
  unsquared-defect-finite-model-invisible: that claim is the finite-dimensional shadow of the literal manuscript group, proved from its compression relations; this one is the corresponding fact for the published torsion-free group, proved from simplicity and Malcev.
  fournier-facio-torsion-free-skeleton: that claim records the construction and the compression core; this one is a representation-theoretic consequence of it.
---

Let `G` be the Fournier-Facio group of `fournier-facio-torsion-free-skeleton`
and `pi(S) <= G` the injectively embedded finitely presented simple
torsion-free group.  Then:

1. every finite-dimensional unitary representation of `G` kills `pi(S)`,
   hence kills the normal closure `<<pi(S)>>`;
2. `G` is not residually finite;
3. if moreover `<<pi(S)>> = G`, then `G` is **minimally almost periodic** —
   every finite-dimensional unitary representation of `G` is trivial.

Clause 3 matters out of proportion to its difficulty.  The hypothesis
`<<pi(S)>> = G` is the strongest form of
`defect-normally-generates-torsion-free-quotient`, the single open
prerequisite of the root's primary route.  So that one group-theoretic fact
would buy **two** things at once: the normal Kazhdan subgroup that
`normal-kazhdan-defect-non-mf` consumes, and minimal almost periodicity of
the source, which is exactly the hypothesis that both open analytic branches
independently ask for (`bounded-rank-corners-excluded` and
`finite-dimensional-models-break-coordinate-generation`).

Clause 1 is unconditional, and it is the Fournier-Facio analogue of the
manuscript's finite-dimensional shadow: no finite-dimensional model detects
anything inside the normal closure of the simple factor, which contains the
compression defect's simple part.
