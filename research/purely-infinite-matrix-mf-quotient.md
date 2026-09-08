---
rg: 2
id: purely-infinite-matrix-mf-quotient
kind: claim
title: At every rank at least two a purely infinite matrix group's MF quotient is its abelianization
distinct_from:
  purely-infinite-unit-group-max-mf-quotient-is-k1: that includes rank one and identifies the canonical algebraic K1 quotient; this proves the elementary and commutator kernel classification directly at all matrix ranks at least two, with no K1 identification.
artifacts:
  - research/artifacts/mf-quotient-proof-validation.json
  - GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientMatrices.lean
---

Let R be any countable unital purely infinite simple ring, n >= 2, and
G = GL_n(R). Let N be the intersection of the kernels of all homomorphisms
from G to operator-norm MF groups. Then

    N = [G,G] = EL_n(R).

The group [G,G] itself has full MF radical. The quotient G/N is the
countable MF group G_ab, and every homomorphism G -> M to an MF group
factors uniquely through G -> G_ab.

This is the higher-rank group-theoretic part of the manuscript's
`thm:mf-quotient-units`. It does not assert the rank-one case or identify
G_ab with the constructed algebraic K1(R).

The Lean endpoint is `MFQuotientMatrices.manuscriptMFQuotientMatrices`;
compilation status is recorded by the targeted Lean workflow for its commit.
