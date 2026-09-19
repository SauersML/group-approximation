---
rg: 2
id: sofic-kernel-amenable-quotient-permanence-proof
kind: route
title: Combine a kernel microstate with a Folner model of the quotient
target: sofic-kernel-amenable-quotient-permanence
requires: []
artifacts:
  - GroupApproximation/Sofic/SoficByAmenablePermanence.lean
  - GroupApproximation/Sofic/SoficIntegerExtension.lean
---

Kernel-checked as
`SoficByAmenablePermanence.isSofic_of_isSofic_of_isAmenable_quotient`.
Choose a set-theoretic section of `G->G/N`.  On a finite Folner set in the
amenable quotient, its displacement cocycle takes only finitely many values
in `N`; approximate those values by permutations and let them act fibrewise
over the Folner set.  Multiplication is exact in each fibre away from the
Folner boundary, while separation comes either from different quotient
levels or from the sofic model of the kernel.  Letting the boundary density
tend to zero gives a sofic approximation of `G`.

The split and nonsplit integer cases are the formal corollaries
`isSofic_int_semidirectProduct` and
`isSofic_of_isSofic_of_int_quotient`.

