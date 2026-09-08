---
rg: 2
id: purely-infinite-canonical-k1-all-ranks
kind: claim
title: Canonical algebraic K1 is the maximal MF quotient at every positive matrix rank and its kernel has full radical
distinct_from:
  purely-infinite-all-rank-mf-quotient: that identifies the quotient with abstract abelianization; this identifies the actual canonical finite-rank stabilization map to algebraic K1 of the base ring and its universal property.
  purely-infinite-matrix-mf-quotient: that identifies the elementary and commutator groups at ranks at least two; this includes rank one, names canonical K1, and proves intrinsic full radical there too.
  purely-infinite-unit-group-max-mf-quotient-is-k1: that is the unit-group statement; this supplies the canonical maps and unique factorization at every positive matrix rank.
  agp-purely-infinite-simple-k1-is-unit-abelianization: that is an algebraic theorem for possibly uncountable rings; this is a countable-ring MF classification with canonical maps at every rank.
artifacts:
  - research/artifacts/canonical-k1-mf-proof-validation.json
  - research/artifacts/canonical-k1-mf-quotient-proof.md
  - GroupApproximation/Manuscript/OneSidedMFRadical/KappaFiniteWitness.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientUnitsKappaProof.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientCanonicalKOne.lean
---

Let R be a countable unital purely infinite simple ring, let n >= 1, and
let kappa_n: GL_n(R) -> K_1(R) be the canonical map to the stable general
linear group modulo its elementary subgroup. Then kappa_n is surjective,

    ker(kappa_n) = [GL_n(R), GL_n(R)] = Rad_MF(GL_n(R)),
    Rad_MF(ker(kappa_n)) = ker(kappa_n),

and K_1(R) is MF. Every homomorphism GL_n(R) -> M to any operator MF group
factors uniquely through kappa_n. The induced quotient isomorphism sends
the class of a matrix A to its actual stable K_1 class.

The analogous assertions for R^x use the canonical map kappa: R^x -> K_1(R).
In particular its kernel, as a group in its own right, has full MF radical.

The closed Lean interfaces are `MFQuotientUnitsKOne.agpUnitKappa`,
`MFQuotientUnitsKOne.manuscriptCanonicalKOne`, and
`MFQuotientUnitsKOne.manuscriptMFQuotientUnitsKOneAtBaseRing`.
They take no AGP or Morita input propositions. General Morita invariance
for arbitrary rings and the uncountable AGP theorem are outside this claim.

This is a completion of the repository's formal proof of a stated
classification, not a claim that the classical AGP identification is new.
