---
rg: 2
id: no-left-orderable-simple-group-has-type-f
kind: claim
title: No left-orderable simple group is of type F
---

Every simple group admitting a left-invariant total order has no finite CW model of
`K(G,1)`.

This is the negative answer to Zaremsky Problem 1.22
(`zaremsky-1-22-left-orderable-simple-group-of-type-f`). It is the negation of
`some-left-orderable-simple-group-has-type-f`.

## Attempts

- (z1-22-lo-simple-bm, 2026-09-13) Two partial obstructions are known or proposed, and
  neither reaches all simple groups.
  - `finite-cd-groups-have-no-micro-supported-line-action` excludes only groups whose
    faithful actions on the line are micro-supported.
  - `irreducible-tree-product-lattices-are-not-left-orderable` (open) would exclude
    lattices in products of boundary-2-transitive tree groups with dense projections.
    It says nothing about simple groups of type F outside such products.
- No mechanism is known that sees finite cohomological dimension of a simple group
  from its dynamics on the line beyond the rigid-stabilizer count. Deferred until the
  lattice case is settled.
- (z1-22-lo-simple-thompson, 2026-09-13) **Dimension lever.** For finitely generated simple groups the
  rigid-stabilizer count is vacuous (`fg-simple-line-groups-have-no-one-sided-supports`). The working lever
  counts disjointly supported elements (`finite-cd-line-groups-bound-disjointly-supported-families`).
  - A nonexistence proof along these lines needs a theorem that every faithful action of a finitely
    generated simple group on the line has unboundedly many disjointly supported nontrivial elements.
  - That theorem must use simplicity: `BS(1,2)` acting by `x ↦ 2x`, `x ↦ x + 1` is of type F with `cd 2`
    and acts minimally, yet no two nontrivial elements have disjoint supports.
  - No such theorem is known to this lane.
