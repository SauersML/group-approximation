---
rg: 2
id: some-type-f-group-has-no-contractible-rips-complex
kind: claim
title: Some group of type F has no contractible Rips complex for any finite generating set and scale
distinct_from:
  some-type-f-group-has-unsolvable-word-problem: that is the Collins–Miller existence of a type-F group with unsolvable word problem; this asks for a type-F group none of whose Rips complexes is contractible
  some-f-infinity-finite-cd-group-has-no-contractible-rips: that is the negative answer to Problem 4.6 over groups of type F_infinity with finite cd, which this one implies; this is the negative answer to Problem 4.7 over groups of type F
  some-amenable-automatic-group-has-no-contractible-rips-complex: that is the negative answer to Problem 4.1 for amenable automatic groups; this is the negative answer to Problem 4.7 for groups of type F
  thompson-f-has-no-contractible-rips-complex: that is the established statement for Thompson's group F, which has infinite cohomological dimension and is not of type F; this asks for a witness of type F
---

There is a group `G` of type F such that for every finite generating set `S` and
every scale `r ≥ 0` the Rips complex `VR_r(G, d_S)` is not contractible.

Equivalently (`group-rips-complexes-are-cayley-graph-flag-complexes`): some group of
type F admits no free, cocompact, vertex-transitive action on a contractible
locally finite flag simplicial complex.

This is the negative answer to Zaremsky's Problem 4.7 under the literal reading;
see `zaremsky-4-07-type-f-groups-have-contractible-rips`.

## Attempts

- A witness must avoid every established positive class: torsion-free asymptotically
  CAT(0) groups, torsion-free coarsely injective groups (including Helly and hierarchically
  hyperbolic groups), finite-edge-group splittings and direct products of such groups
  (see the root). Dimension obstructions such as `thompson-f-has-no-contractible-rips-complex`
  are unavailable, since a group of type F has a finite `K(G,1)`.
- A proof must control EVERY finite generating set at EVERY scale. Coarse invariants do
  not do this directly: the Rips system of a group of type F is essentially contractible,
  so each homotopy class dies at a larger scale, and a witness needs new classes born at
  every scale for every generating set. No mechanism for that is known here yet.
- From z4-06-rips-finf-fcd: a counterexample `G` to Problem 1.21 (type `F_∞`, finite cd, not
  of type F) makes `G × Z` of type F, and none of its Rips complexes for product generating
  sets is contractible (`counterexample-times-z-lacks-contractible-product-rips`).
  Non-product generating sets remain.
- Test objects: groups of type F with distorted infinite cyclic subgroups, such as the
  integral Heisenberg group and `BS(1,2)`.
- 2026-09-16 (swarm, refereed): neither test object is a witness. Every `BS(m,n)` has a
  2-dimensional contractible scale-1 Rips complex
  (`baumslag-solitar-groups-have-contractible-rips-complexes`). `H_3(Z)` has a scale-1
  Rips complex homeomorphic to `R^3`
  (`heisenberg-group-has-a-contractible-rips-complex`). So distortion, exponential or
  cubic Dehn functions, non-automaticity and non-Hopficity do not by themselves obstruct.
  Where both methods stop is recorded in
  `notes/some-type-f-group-has-no-contractible-ri-swarm-2026-09-16.md`.
