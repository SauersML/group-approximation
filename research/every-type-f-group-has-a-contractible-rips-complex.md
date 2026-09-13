---
rg: 2
id: every-type-f-group-has-a-contractible-rips-complex
kind: claim
title: Every group of type F has a contractible Rips complex for some finite generating set and scale
distinct_from:
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's theorem for the single group Z^n with its standard generators; this quantifies over all groups of type F and allows any generating set
  hyperbolic-rips-complex-models-proper-actions: that is the Meintrup–Schick model for proper actions of hyperbolic groups; this is a universal statement over groups of type F
---

For every group `G` of type F there are a finite generating set `S` and a scale
`r ≥ 0` such that the Rips complex `VR_r(G, d_S)` is contractible.

Equivalently (`rips-complex-of-a-group-is-a-flag-cayley-complex`): every group of
type F acts freely, cocompactly and transitively on the vertices of a contractible
locally finite flag simplicial complex.

This is the affirmative answer to Zaremsky's Problem 4.7 under the literal reading;
see `zaremsky-4-07-type-f-groups-have-contractible-rips`.

## Attempts

- Classes known or reported: hyperbolic groups, `Z^n`, two-dimensional RAAGs,
  graphs of groups with finite edge groups over type-R vertex groups, all RAAGs
  with the commuting-products generating set, groups satisfying Zaremsky's Link
  Criterion (see the root for sources).
- Planned (z4-07-type-f-rips): groups acting properly and coboundedly on injective
  metric spaces, by pushing a farthest vertex inward with the binary ball
  intersection property. Where it stops: groups with no coarsely injective
  geometry, since coarsely injective groups are semihyperbolic and so have
  quadratic Dehn function (Haettel–Hoda–Petyt, Geom. Topol. 27 (2023), abstract),
  which excludes `BS(1,2)` and the Heisenberg group from that method.
