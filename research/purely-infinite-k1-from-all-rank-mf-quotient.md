---
rg: 2
id: purely-infinite-k1-from-all-rank-mf-quotient
kind: route
title: The canonical all-rank proof closes the unit K1 headline without an AGP import
target: purely-infinite-unit-group-max-mf-quotient-is-k1
requires:
  - purely-infinite-canonical-k1-all-ranks
artifacts:
  - GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientUnitsKappaProof.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientCanonicalKOne.lean
---

The prerequisite explicitly includes R^x and its canonical kappa, with
commutator kernel, intrinsic full radical of that kernel, and unique
factorization to MF targets. Its quotient is the constructed algebraic K1.
The rank-one Lean endpoint is `manuscriptMFQuotientUnitsKOne`; the
intrinsic kernel conclusion is `unit_commutator_full_mf_radical` together
with `agpUnitKappa`.

If K1 is trivial, every MF-target homomorphism is trivial by factorization.
Conversely, if the unit group has full MF radical, its surjective map to
the countable abelian MF group K1 is trivial, so K1 is trivial.

