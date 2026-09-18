---
rg: 2
id: twisted-brin-thompson-groups-have-property-fa
kind: claim
title: Every twisted Brin-Thompson group has no loxodromic actions, so every finitely generated one has Serre's property FA
distinct_from:
  fg-perfect-wreath-c2-has-property-fa: that certifies FA for one wreath square of a perfect group by an axis argument, and the resulting envelope is not simple; this certifies FA, and more, for the simple groups SV_G by importing property NL, with no hypothesis on G or on the action.
  property-t-implies-property-fa: that obtains FA from property (T), which is not asserted for twisted Brin-Thompson groups; this obtains FA from the absence of loxodromic elements in actions on hyperbolic spaces.
  twisted-brin-thompson-finite-presentation-criterion: that is a finiteness criterion for SV_G and says nothing about fixed points; this is a fixed-point property of SV_G and needs only finite generation.
  decidable-groups-embed-in-decidable-simple-fa-groups: that is the universal embedding statement for decidable inputs; this is the fixed-point ingredient it consumes, applied to the self-twisted host G.V_G.
---

**ESTABLISHED** (literature import with a written check) by
`twisted-brin-thompson-groups-have-property-fa-citation`.

Let a group `G` act on a non-empty set `S`, and let `SV_G` be the (abstract)
twisted Brin--Thompson group. When the action is faithful this is the twisted
Brin--Thompson group of Belk--Zaremsky.

1. **(NL)** Every action of `SV_G` by isometries on a hyperbolic space is
   elliptic or parabolic; in particular no element acts loxodromically.
2. **(FW_infty)** Every action of `SV_G` on a finite-dimensional CAT(0) cube
   complex has a global fixed point.
3. **(FA)** If `SV_G` is finitely generated (by Belk--Zaremsky Theorem A: `G`
   finitely generated with finitely many orbits on `S`), then every action of
   `SV_G` on a tree has a global fixed point.

Part 3 follows from Part 1 alone with Serre's lemma. Part 2 gives it again,
since a tree is a one-dimensional CAT(0) cube complex. So the two imports give
independent certificates.

## Why this matters

Twisted Brin--Thompson hosts are the standard computable simple envelopes.
For `S = G` with the translation action, `G.V_G` is a finitely generated
simple group that contains `G`, and it has solvable word problem exactly when
`G` does (`self-twisted-bt-group-fp-embedding-iff-solvable-wp`). With this
claim it is also FA, which settles
`decidable-groups-embed-in-decidable-simple-fa-groups`.

It also marks where Helly-type hand proofs of FA for these groups stop being
necessary. Attempt 3 of `decidable-groups-embed-in-decidable-simple-fa-groups`
died at the pairwise-join step for cone-supported generators. The imported
proof avoids joins entirely: it goes through uniform perfectness (which kills
quasimorphisms, hence focal and oriented lineal actions) and relative
simplicity (which kills general-type actions).
