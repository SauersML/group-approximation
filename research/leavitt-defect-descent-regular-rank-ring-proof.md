---
rg: 2
id: leavitt-defect-descent-regular-rank-ring-proof
kind: route
title: Replace each ultraproduct step of the defect chain by regular-ring conservation, Sylvester corner locality, corners and ultraproducts of regular rank rings
target: leavitt-defect-descent-chain-holds-in-regular-rank-rings
requires:
  - regular-rank-ring-compressors-conserve-fixed-right-ideals
  - corner-defect-killing-rank-functions-are-augmentation
  - leavitt-gl-equals-el-and-perfect-unit-group
  - binary-leavitt-unit-group-is-simple
  - binary-leavitt-unit-group-four-generated
  - leavitt-cylinder-swaps-generate-thompson-in-el
  - leavitt-unit-group-carries-nontrivial-rigid-defect
  - leavitt-packet-linear-sofic-kills-kaplansky-target
artifacts:
  - research/artifacts/rank-gate-axiom-audit-2026-09-12.md
  - research/artifacts/two-root-defect-descent-gap-2026-09-12.md
  - research/artifacts/two-root-defect-piece-and-fd-representations-2026-09-12.md
---

Artifact Theorem 3.1. The proofs of the defect-piece and descent artifacts go through, with these
replacements.
- **Principal fixed ideals and globality in degree `(1,0)`.** `regular-rank-ring-compressors-conserve-fixed-right-ideals`,
  with the compressor generation and simplicity inputs of `leavitt-rank-models-fixed-ideals-proof`.
- **Corner locality.** `corner-defect-killing-rank-functions-are-augmentation`, applied to the pullback of
  the rank of `U`.
- **Corner models.** A nonzero corner of a faithful regular rank ring, renormalized, is again one
  (artifact Lemma 2.1(1)).
- **Compactness.** An ultraproduct of faithful regular rank rings, modulo its null ideal, is again one
  (artifact Lemma 2.1(2)). The limit homomorphism has zero corner product and positive displacement,
  contradicting corner locality.
- **Unchanged.** The dimension calculus of principal right ideals, square zero in characteristic two,
  commuting disjoint cylinders and `V`-transitivity, perfection, and four-generation.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 18.3, as a step-by-step transfer of Section 8 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
