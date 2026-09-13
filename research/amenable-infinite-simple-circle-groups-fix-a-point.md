---
rg: 2
id: amenable-infinite-simple-circle-groups-fix-a-point
kind: claim
title: An amenable infinite simple group acting faithfully on the circle fixes a point, so it acts faithfully on the line
distinct_from:
  no-proper-character-groups-avoid-amenable-orbit-full-groups: that excludes groups without proper characters from amenable-orbit realizations, a measure-theoretic certificate for soficity; this is a topological statement about circle actions of amenable simple groups
  amenable-full-group-forces-invariant-measure: that turns amenability of a full group into an invariant measure on a Cantor unit space and removes compressible groupoids; this uses the invariant measure on the circle and removes fixed-point-free circle actions of simple groups
---

**ESTABLISHED.** Let `S` be an infinite simple group and `rho : S -> Homeo(S^1)` a
nontrivial homomorphism. If `S` is amenable, then `rho(S)` has a global fixed point
`p`, and `S` acts faithfully on `S^1 \ {p} ≅ R` by orientation-preserving
homeomorphisms.

Equivalently: an infinite simple group with an action on the circle without a
global fixed point is non-amenable.

**Consequences for `fp-infinite-simple-amenable-group`.**
- An example acting faithfully on the circle is a group of homeomorphisms of the
  line.
- Thompson's `T` and Lodha's finitely presented simple circle group act on the
  circle without a global fixed point, so they are non-amenable. Both were
  already recorded dead through other routes.
- A group of homeomorphisms of `R` commuting with `t -> t + 1` acts on the circle.
  If it is infinite and simple and that circle action has no global fixed point, it
  is non-amenable. Hyde–Lodha's finitely presented simple groups are of this kind:
  `hyde-lodha-periodic-simple-groups-are-not-amenable`.

**Model test.** `F'` acting on `[0,1]/(0 ~ 1)` is infinite and simple and fixes the
point `0`; its amenability is open, and the statement correctly says nothing about
it. Thompson's `T` is simple, acts without a global fixed point, and contains `F_2`,
as the statement requires.

**Novelty.** None claimed. The non-atomic case is the classical semiconjugacy of a
measure-preserving group of circle homeomorphisms to a group of rotations.

Route: `amenable-infinite-simple-circle-groups-fix-a-point-proof`.
