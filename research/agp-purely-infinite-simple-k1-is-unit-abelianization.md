---
rg: 2
id: agp-purely-infinite-simple-k1-is-unit-abelianization
kind: claim
title: For a purely infinite simple ring K_1 is the abelianization of the unit group
distinct_from:
  ge-ring-with-perfect-units-has-gl-equals-el: that is the elementary consequence of the GE property once the unit group is already perfect; this is the literature theorem identifying the obstruction group, and it is what turns a K_1 computation into perfection.
  leavitt-gl-equals-el-and-perfect-unit-group: that proves perfection of one unit group internally, with no K-theory at all; this is the general external theorem that an alternative route would use instead.
artifacts:
  - research/artifacts/rank-one-headline-review-2026-09-07.md
---

**Established by citation.**  Ara--Goodearl--Pardo, arXiv:math/0111066,
Theorem 2.4, quoted:

> If `R` is a purely infinite simple ring then `K_1(R) = U(R)^ab`.

No von Neumann regularity is assumed, despite the paper's title; their proof
records that a purely infinite simple ring is a GE-ring, so the natural map
`U(R) -> K_1(R)` is surjective.  Their Theorem 4.2 supplies that the Leavitt
algebra `V_(1,n)` of type `(1,n)` is purely infinite simple for `n >= 2`.

So `K_1(R) = 0` makes `R^x` perfect for such a ring.

## Internal proof for the countable subcase

`MFQuotientUnitsKOne.agpUnitKappa`, in
`GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientUnitsKappaProof.lean`,
now proves surjectivity and the exact commutator kernel for countable R
using finite stabilized commutators and explicit supported-unit compression.
`purely-infinite-canonical-k1-all-ranks` integrates this with the complete
canonical MF classification. The present claim still covers uncountable
rings, so its citation route is retained; the countable proof is not
asserted to discharge that larger quantifier scope.
