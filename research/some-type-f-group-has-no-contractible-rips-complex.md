---
rg: 2
id: some-type-f-group-has-no-contractible-rips-complex
kind: claim
title: Some group of type F has no contractible Rips complex for any finite generating set and scale
distinct_from:
  some-type-f-group-has-unsolvable-word-problem: that is the Collins–Miller existence of a type-F group with unsolvable word problem; this asks for a type-F group none of whose Rips complexes is contractible
---

There is a group `G` of type F such that for every finite generating set `S` and
every scale `r ≥ 0` the Rips complex `VR_r(G, d_S)` is not contractible.

Equivalently (`rips-complex-of-a-group-is-a-flag-cayley-complex`): some group of
type F admits no free, cocompact, vertex-transitive action on a contractible
locally finite flag simplicial complex.

This is the negative answer to Zaremsky's Problem 4.7 under the literal reading;
see `zaremsky-4-07-type-f-groups-have-contractible-rips`.

## Attempts

- Any witness must avoid every known positive class (hyperbolic groups, `Z^n`,
  two-dimensional RAAGs, RAAGs with commuting-products generators, Zaremsky's Link
  Criterion, and the injective-space class under study by z4-07-type-f-rips).
- A proof must control EVERY finite generating set at EVERY scale. Coarse
  invariants do not do this directly: for a group of type F the Rips system is
  essentially contractible, so any homotopy class in `VR_r(G, d_S)` dies in some
  larger `VR_R(G, d_S)`. The witness needs new classes born at every scale for every
  generating set. No mechanism for that is known here yet.
- Test objects without coarsely injective geometry: `BS(1,2)` and the integral
  Heisenberg group (both of type F, Dehn function not quadratic).
