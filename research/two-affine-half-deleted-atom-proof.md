---
rg: 2
id: two-affine-half-deleted-atom-proof
kind: route
title: Classify two affine hyperplanes and charge overlap or deleted-atom loss
target: two-affine-half-rows-pay-deleted-dyadic-atom
requires:
  - dyadic-pauli-payload-flags-supply-strict-target-capacity
  - affine-reflection-normalizers-have-quarter-overlap
---

Exactify the fixed flag packet and its finite normalizer table.  A normalizer
sends the source sign half to an affine hyperplane of the uniform joint flag
atoms.  Compress the two normalizer unitaries by the target complement
`F=C-D`.  Their diagonal Gram losses are exactly the masses of `D` in the two
image hyperplanes, while the crossed Gram is exactly the intersection of the
two hyperplanes outside `D`.

Two affine hyperplanes are equal, complementary, or transverse.  Their
intersection masses are respectively `1/2`, `0`, and `1/4` of the payload.
In the complementary case exactly one contains `D`; in the transverse case
deleting `D` removes at most its own mass and its membership terms restore
that loss.  The sum of the three squared row defects is therefore at least
`tau(D)=2^(-n)tau(C)`.  Fixed finite-group normalized-HS correction changes
this by only `O_n(sqrt(E_pres))`.
