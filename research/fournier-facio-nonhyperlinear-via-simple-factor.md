---
rg: 2
id: fournier-facio-nonhyperlinear-via-simple-factor
kind: route
title: A non-hyperlinear simple factor excludes every Fournier--Facio singular near witness
target: fournier-facio-has-no-purely-singular-free-near-representation
requires:
  - fournier-facio-hyperlinear-iff-singular-near
  - fournier-facio-nontrivial-quotients-contain-simple-wreath
  - fournier-facio-simple-factor-not-hyperlinear
---

A purely singular essentially free near representation of `G` would make `G`
hyperlinear, by the established equivalence.  `G` contains `S wr Z` and in
particular `S` (clause (W8) applied to the identity homomorphism).  Subgroups
of hyperlinear groups are hyperlinear, so `S` would be hyperlinear, contrary
to the third prerequisite.

The prerequisite is strictly stronger than the target and concerns a
different group, so this route is a genuine reduction, not a restatement.
The heredity clause gives more than the target needs: under the same
prerequisite, every nontrivial tracial model of `G` in an
`R^omega`-embeddable algebra is trivial.
