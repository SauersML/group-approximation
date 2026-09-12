---
rg: 2
id: purely-infinite-canonical-k1-proof
kind: route
title: Finite stable commutators compress to supported units and give the canonical all-rank quotient
target: purely-infinite-canonical-k1-all-ranks
requires:
  - full-complementary-idempotent-elementary-full-mf-radical
  - purely-infinite-matrix-mf-quotient
  - purely-infinite-all-rank-mf-quotient
artifacts:
  - research/artifacts/canonical-k1-mf-quotient-proof.md
  - GroupApproximation/Manuscript/OneSidedMFRadical/KappaFiniteWitness.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientUnitsKappaProof.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientCanonicalKOne.lean
---

The artifact gives the full argument. The existing elementary/commutator
equality makes a canonical K1-trivial unit a commutator after finite
stabilization: images of finite-rank commutator groups form a directed
union, and equality of colimit representatives means equality at a common
later rank.

An explicit matrix-corner homomorphism returns any supported unit from
its stabilized diagonal. It therefore pulls its finite commutator
witness back to the original unit group. The already proved arbitrary-unit
Peirce reduction changes a unit only by an element of the corner-unit
subgroup, which lies in the commutator subgroup. This proves the reverse
canonical kernel inclusion. Gaussian elimination supplies surjectivity.

Apply Gaussian elimination once more to finite matrices. The canonical
class of EAF=diag(u,1,...,1) is kappa(u), so canonical triviality forces
u, and hence A, into the commutator subgroup. This proves the exact
base-ring kernel without assuming general Morita invariance.

Finally the corner-unit subgroup has full MF radical intrinsically,
because a homomorphism defined on that subgroup restricts to a trivial
map on every elementary source that generates it. The supported-unit
reduction identifies it with the unit commutator subgroup. Applying this
to each matrix ring includes rank one in the intrinsic radical theorem.

