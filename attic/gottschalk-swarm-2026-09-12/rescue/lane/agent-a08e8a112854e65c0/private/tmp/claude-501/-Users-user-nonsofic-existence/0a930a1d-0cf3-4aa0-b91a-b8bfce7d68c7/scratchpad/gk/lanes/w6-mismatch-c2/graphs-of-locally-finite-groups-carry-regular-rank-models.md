---
rg: 2
id: graphs-of-locally-finite-groups-carry-regular-rank-models
kind: claim
title: Graphs of locally finite subgroups of the binary Leavitt unit group carry weakly finite char-2 rank models with independent cylinder defects
distinct_from:
  locally-finite-hnn-data-allow-independent-cylinder-defects: that is one locally finite vertex group with single-letter partial conjugations; this allows any countable graph of locally finite vertex groups, so forest edges amalgamate different locally finite subgroups and products of their elements are realized as products.
  binary-locally-finite-hnn-models-violate-two-root-identity: that is the letterwise model over one locally finite base; this adds amalgamation along intersections of several locally finite subgroups.
  commuting-subgroup-witnesses-cannot-distort-defect-ranges: that is a product model of a locally finite subgroup with a commuting rank-modelled subgroup; this is the fundamental group of an arbitrary graph of locally finite groups, with no commutation hypothesis.
  fock-local-letters-extend-level-models-with-disjoint-commutation: that realizes exact commutation of disjointly supported letters but not partial conjugations across supports; this realizes partial conjugations and amalgamated products but not commutation between elements of different vertex groups.
artifacts:
  - research/artifacts/mismatched-factor-graph-of-groups-firewall-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w6-mismatch-c2`; verification requested from `w4-vf-gate`) by
`graphs-of-locally-finite-groups-regular-models-proof`. Artifact Section 1.

**Setting.** `R = L_(F_2)(1,2)`. Let `Y` be a countable graph of groups whose vertex groups `L_v` are countable
locally finite subgroups of `R^x`, and whose edges `e : v -> w` carry a unit `u_e` and a subgroup
`K_e <= L_v cap u_e^-1 L_w u_e` identified with `u_e K_e u_e^-1`, where `u_e = 1` on a chosen maximal forest.
Let `pi_1(Y)` be its fundamental group.

**Statement.** There is a homomorphism `sigma : pi_1(Y) -> M^x` into a characteristic-two rank ultraproduct with:
1. the free profile `rk(sigma(alpha)) = rank(lambda_Q(alpha))/|Q|` on every finite subgroup `Q` of every vertex
   group;
2. `sigma` nontrivial, and fixed-point-free when some vertex group is infinite;
3. every `M_k(M)` directly finite, so `sigma` is a weakly finite representation.

If the unit root pairs of pairwise disjoint proper cylinders `A_1, ..., A_k` lie in one vertex group, then
`rk(sigma(D_A)) = 3/8` and `rk(sigma(D_(A_1) ... D_(A_k))) = (3/8)^k`, so `theta = 1` and `sigma(D_A) != 0`.

**Consequence.** No argument for `leavitt-disjoint-cylinder-defects-strictly-submultiplicative`, for
`sylvester-rank-functions-on-leavitt-units-kill-two-root-defect`, or for
`binary-complement-corner-has-no-weakly-finite-image` in its representation form can use only:
* relations holding in `pi_1(Y)` for one such graph containing the configurations used, including products of
  elements from different amalgamated vertex groups and conjugation chains routed through their intersections;
* rank calculus in rank ultraproducts, nontriviality and fixed-point-freeness.

Such an argument must use a relation of `R^x` that fails in every such `pi_1(Y)` containing its letters, such as
commutation between elements of different vertex groups that lie in no common vertex group, or a global input
about all models of `R^x`.
