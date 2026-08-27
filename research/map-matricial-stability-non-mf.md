---
rg: 2
id: map-matricial-stability-non-mf
kind: claim
title: A minimally almost periodic matricially stable group is not MF
distinct_from:
  normal-kazhdan-defect-non-mf: that claim obtains non-MF-ness from a normal Kazhdan subgroup in the compression defect and proves its own rigidity; this one assumes a stability hypothesis outright and needs no compression data at all.
  central-sign-corona-obstruction: that claim marks a central involution; this one has no mark and no torsion anywhere in its statement.
---

Let `G` be an infinite countable group that is **minimally almost
periodic** — every finite-dimensional unitary representation is trivial —
and **matricially stable** in Dadarlat's sense: for every asymptotic
homomorphism `phi_n : G -> U(k_n)`, not necessarily separating, there are
homomorphisms `pi_n : G -> U(k_n)` with `‖phi_n(s) - pi_n(s)‖ -> 0` for each
`s in G`.  Then `G` is not MF.

The argument is two lines and is written out in the proof route.  What makes
it worth a node is its shape: **no torsion, no mark, no central element, no
compression data**.  It is the cleanest torsion-free-compatible non-MF
criterion available, and its group-theoretic hypothesis is one this program
is already forced into from two other directions
(`bounded-rank-corners-excluded`,
`finite-dimensional-models-break-coordinate-generation`).

The price is the stability hypothesis, which is unproved for every candidate
here and is the same wall the repository already records for its Steinberg
group: proving operator-norm stability for `St_5(L)` would close the weak-MF
lane negatively, while proving weak MF would exhibit an explicit failure of
that stability.  This node states the implication cleanly so that the wall
has a name in the graph.

## Ideas

**Stronger unconditional criterion, now source-checked.**  Two statements in
Dadarlat, arXiv:2007.12655v2, combine directly:

- MF implies weak quasidiagonality;
- Proposition 3.19, attributed to Ozawa--Thom: an infinite property-(T)
  group that is weakly quasidiagonal has an infinite residually finite
  quotient.

Chained, these give: *an infinite Kazhdan group with no infinite residually
finite quotient is not MF*.  Both statements and the proof of Proposition
3.19 were checked in the primary PDF; no `gamma`-element, stability or
linearity hypothesis enters this implication.  The simple-group consequence
and its full-radical upgrade are recorded in
`simple-kazhdan-groups-have-full-mf-radical`.  This strictly strengthens the
present stability criterion on infinite simple Kazhdan groups, while the
present criterion remains useful for minimally almost periodic groups
without property `(T)`.
