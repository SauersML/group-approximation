---
rg: 2
id: purely-infinite-k1-from-all-rank-mf-quotient
kind: route
title: The explicit MF-kernel proof leaves only the canonical K1 identification
target: purely-infinite-unit-group-max-mf-quotient-is-k1
requires:
  - purely-infinite-all-rank-mf-quotient
  - agp-purely-infinite-simple-k1-is-unit-abelianization
artifacts:
  - research/purely-infinite-all-rank-mf-quotient-proof.md
  - GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientUnitsMatrixReduction.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientUnitsKappaResidue.lean
---

The first prerequisite gives Rad_MF(R^x)=[R^x,R^x], intrinsic full MF radical
of that commutator subgroup, and unique factorization through abelianization.
It also proves that the quotient is countable abelian and MF. Its MF-kernel
proof uses the explicit arbitrary-unit and supported-unit constructions;
it does not require the canonical algebraic K1 identification.

The second prerequisite identifies the canonical map kappa:R^x -> K1(R)
as surjective with kernel [R^x,R^x]. The quotient theorem therefore identifies
R^x/Rad_MF(R^x) with K1(R), and the universal property transports to kappa.
It also follows that R^x has full MF radical exactly when K1(R) is trivial.

This route separates two kinds of evidence: the all-rank group-theoretic
kernel endpoint is implemented in Lean, while the canonical K1 prerequisite
remains the graph's explicit literature import of AGP Theorem 2.4. It does
not treat an arbitrary abelian quotient as the constructed canonical K1.
