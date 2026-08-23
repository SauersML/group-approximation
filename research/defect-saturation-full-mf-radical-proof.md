---
rg: 2
id: defect-saturation-full-mf-radical-proof
kind: route
title: Route the simple compression defect onto a torsion-free Kazhdan quotient
target: defect-saturation-full-mf-radical
requires:
  - fournier-facio-torsion-free-skeleton
  - defect-normally-generates-torsion-free-quotient
  - normal-kazhdan-defect-non-mf
artifacts:
  - research/artifacts/hyperlinear-to-mf-saturation-compiler-2026-08-22.md
  - research/artifacts/router-detector-torsion-free-non-mf-2026-08-22.md
  - research/artifacts/torsion-free-full-mf-radical-2026-08-19.md
  - GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean
  - GroupApproximation/Sofic/ManuscriptClosedWrappers.lean
---

## Why sufficient

Start from the finitely presented torsion-free property-(T) compression source
of `fournier-facio-torsion-free-skeleton`.  Its compression defect contains a
copy of the nonabelian simple torsion-free group `S`; the simple-subgroup
saturation step is independently kernel-checked in
`FournierFacioDefectData.simpleSubgroup_le_defectNormal`.

`defect-normally-generates-torsion-free-quotient` supplies the audited
Hull--Osin quotient `q : G ->> Q` with the following simultaneous properties:
`Q` is two-generated, finitely presented, torsion-free and acylindrically
hyperbolic; a protected nontrivial element of `S` survives; and
`Q = <<q(S)>>^Q`.  Property (T) passes through the second common-quotient map
from the torsion-free hyperbolic Kazhdan factor `H ->> Q` (not from the HNN
source `E`).

The image of the compression defect is normal and contains `q(S)`: a
nontrivial commutator with the protected element gives a nontrivial normal
intersection with the nonabelian simple group `q(S)`, hence contains all of
`q(S)`.  Since `q(S)` normally generates `Q`, the mapped defect is all of
`Q`.  Apply `normal-kazhdan-defect-non-mf` to the mapped compression core with
normal Kazhdan subgroup `K = Q`.  Every norm-matrix-corona homomorphism kills
all of `Q`, so `Res_MF(Q)=Q`.  The protected element makes `Q` nontrivial.

Finally, full MF residual passes through every surjective homomorphism
(`coronaMFResidual_eq_top_of_surjective` in the Lean artifact), so every
nontrivial quotient `L` of `Q` also satisfies `Res_MF(L)=L` and is non-MF.
