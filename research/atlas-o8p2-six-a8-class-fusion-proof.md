---
rg: 2
id: atlas-o8p2-six-a8-class-fusion-proof
kind: route
title: Compute affine complement fusion in the degree-135 O8+(2) action
target: atlas-o8p2-has-six-triality-a8-classes
requires:
  - atlas-o8p2-carrier-a8-classes-and-absorption
---

Construct `G=PrimitiveGroup(135,2)` and take a point stabilizer
`M=2^6:A8`.  Its unique normal elementary abelian subgroup of order 64 has
two complement classes.  Ambient normalizers have structures `A8` and `S8`,
and the two complements are not `G`-conjugate.  Direct containment counting
in the 135 point stabilizers gives incidences one and two, proving `(O8F2)`.

Next compute the seventeen maximal-subgroup class representatives of `G`.
For each of the three affine triality classes, repeat the complement
calculation.  The exact six-by-six ambient conjugacy matrix is the identity:
all six complements are pairwise nonconjugate.  Their normalizer multiset is
three copies each of 20160 and 40320.

For each `S6(2)` maximal representative, take the unique maximal `S8` whose
derived subgroup is `A8`; for each `A9`, take its unique maximal `A8`.
Ambient conjugacy tests match the three natural representatives bijectively
to the 20160-normalized complement classes and the three orthogonal
representatives bijectively to the 40320-normalized classes.  The established
maximal-carrier fork says every `A8<G` appears in one of these carriers, so
the list is complete.

