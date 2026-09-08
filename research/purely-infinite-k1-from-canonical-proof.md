---
rg: 2
id: purely-infinite-k1-from-canonical-proof
kind: route
title: Canonical K1 maps give unique extension of MF representations to every matrix rank
target: mf-representations-of-units-extend-under-stabilization
requires:
  - purely-infinite-canonical-k1-all-ranks
artifacts:
  - GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientUnitsKappaProof.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientCanonicalKOne.lean
  - research/artifacts/canonical-k1-mf-quotient-proof.md
---

Let iota_n(u)=diag(u,1,...,1). The checked identity
`matrixKappa_diagAt` gives kappa_n composed with iota_n equal to kappa.
For any MF group M, write a given f:R^x->M uniquely as h composed with
kappa, using the rank-one universal property. Then F=h composed with
kappa_n extends f to GL_n(R).

If F' is another extension, the all-rank universal property writes
F'=h' composed with kappa_n. Restriction gives h' composed with kappa=f.
Since kappa is surjective, h'=h, hence F'=F. Thus restriction along the
specified diagonal inclusion is bijective.

This route uses the actual canonical maps and their checked compatibility;
it needs neither a projective-module classification nor a general Morita
invariance input. Its explicit Lean ingredients are
`manuscriptMFQuotientUnitsKOne`, `factors_uniquely_through_matrixKappa`,
and `matrixKappa_diagAt`.
