---
rg: 2
id: some-left-orderable-simple-group-has-type-f
kind: claim
title: Some left-orderable simple group is of type F
---

There is a group `G` that is simple, admits a left-invariant total order, and has a
finite CW model of `K(G,1)`.

This is the affirmative answer to Zaremsky Problem 1.22
(`zaremsky-1-22-left-orderable-simple-group-of-type-f`).

**Constraints on any witness.**

- `G` is finitely presented, torsion-free, infinite, and `cd G < ∞`.
- `G` has no proper finite-index subgroup, since a finite quotient of a simple infinite
  group is trivial.
- In any faithful action of `G` on `R`, at most `cd G` pairwise disjoint open intervals
  have nontrivial rigid stabilizers. So no faithful action of `G` on `R` is
  micro-supported (`finite-cd-groups-have-no-micro-supported-line-action`).

## Attempts

- (z1-22-lo-simple-bm, 2026-09-13) Torsion-free simple lattices in products of two
  trees are of type F, so one left-orderable lattice would do:
  `some-left-orderable-simple-group-has-type-f-via-burger-mozes`.
- (z1-22-lo-simple-bm, 2026-09-13) Thompson-like groups of homeomorphisms of the line
  (Hyde–Lodha, arXiv:2302.04805) are type F∞ but their natural actions are
  micro-supported, which forces infinite cohomological dimension. A witness from that
  world needs a group all of whose faithful actions on `R` are far from micro-supported.
  Peer lane z1-22-lo-simple-thompson.
