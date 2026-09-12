---
rg: 2
id: purely-infinite-all-rank-mf-quotient
kind: claim
title: The MF radical of every general linear group over a countable purely infinite simple ring is its commutator subgroup
distinct_from:
  purely-infinite-matrix-mf-quotient: that gives the direct elementary-group proof for n at least two; this includes the unit group at rank one by an explicit arbitrary-unit reduction.
  purely-infinite-unit-group-max-mf-quotient-is-k1: that additionally identifies the quotient with canonical algebraic K1; this proves the full group-theoretic classification without taking that identification as an input.
artifacts:
  - research/artifacts/mf-quotient-proof-validation.json
  - GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientUnitsMatrixReduction.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientUnitsPeirce.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientUnitsReductionProof.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientUnitsStepOne.lean
---

For every countable unital purely infinite simple ring R and every n >= 1,
write G = GL_n(R). Then

    Rad_MF(G) = [G,G].

Thus G/Rad_MF(G) is its countable abelian MF abelianization, and every
homomorphism from G to an MF group factors uniquely through abelianization.
The commutator subgroup itself has full MF radical, as the generating-family
argument in the proof route shows.
There are no AGP or Menal--Moncasi input propositions in this assertion.

The arbitrary-unit reduction is stronger than needed: every u in R^x is
congruent modulo `cornerUnitSubgroup R` to a unit fixing a nonzero idempotent.
The endpoint `MFQuotientUnits.manuscriptMFQuotientUnits` supplies the all-rank
kernel equality and countable abelian MF quotient. The Peirce reduction and
supported-unit theorem discharge its two substantive rank-one inputs.
The intrinsic-radical consequence at rank one is proved in the mathematical
route; the current Lean endpoint does not separately export that consequence.

This claim does not identify that quotient with the separately constructed
canonical algebraic K1. It uses the full-defect theorem, whose existing proof
uses property (T); it makes no property-(T)-free or nonhyperlinear claim.

The consuming Lean build and closed endpoint audit passed at
`6f8cc618518800db40b000e8b6b4856a07eeda4a` and were merged to main in
`c2d5f6518d7aa2e03236b7399ac9f01baa9cc2aa`. The validation artifact records
source hashes, CI links, and the precise formal coverage.
