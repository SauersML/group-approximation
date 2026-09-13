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
- In any faithful action of `G` on `R`:
  - at most `cd G` nontrivial elements have pairwise disjoint supports
    (`finite-cd-line-groups-bound-disjointly-supported-families`);
  - every rigid stabilizer of a proper subinterval of a component of `R ∖ Fix(G)` is trivial
    (`fg-simple-line-groups-have-no-one-sided-supports`).

## Attempts

- (z1-22-lo-simple-bm, 2026-09-13) Torsion-free simple lattices in products of two
  trees are of type F, so one left-orderable lattice would do:
  `some-left-orderable-simple-group-has-type-f-via-burger-mozes`.
- (z1-22-lo-simple-bm, 2026-09-13; corrected) Thompson-like groups of homeomorphisms of the line
  (Hyde–Lodha, arXiv:2302.04805) are of type F∞, but their infinite dimension comes from
  disjointly supported families, which no witness can contain. See the peer bullets below.
  Peer lane z1-22-lo-simple-thompson.
- (z1-22-lo-simple-thompson, 2026-09-13) **Thompson-like upgrades: dead.** The route
  `lo-simple-type-f-via-thompson-like-subgroups` is invalidated by
  `finite-cd-line-groups-bound-disjointly-supported-families`. A group of finite cohomological
  dimension has at most `cd G` nontrivial elements with pairwise disjoint supports (of any shape), so it
  contains no `F'` and no `Z ≀ Z`. The Hyde–Lodha groups `G_ρ` contain `F'`
  (`hyde-lodha-groups-contain-thompson-commutator-subgroup`).
- (z1-22-lo-simple-thompson, 2026-09-13) **Correction on micro-support.** A finitely generated simple
  group acting faithfully on the line has no nontrivial rigid stabilizer on any proper subinterval of a
  component, has faithful end germs, and has no finite-breakpoint PL or finitely piecewise projective
  faithful action (`fg-simple-line-groups-have-no-one-sided-supports`).
  - So the natural actions of the Hyde–Lodha simple groups are not micro-supported, and the
    micro-support count never excludes a simple candidate.
  - Their infinite dimension is detected by disjoint non-interval supports such as those of
    `λ(F') ≤ G_ρ`.
