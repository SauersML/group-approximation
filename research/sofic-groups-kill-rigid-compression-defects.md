---
rg: 2
id: sofic-groups-kill-rigid-compression-defects
kind: claim
title: A sofic group containing an infranormal Kazhdan pair has trivial rigid compression defect
distinct_from:
  kun-thom-sofic-centralizer-normalization: that is the ultraproduct normalization theorem for sofic representations of the pair; this is its group-level form for an arbitrary sofic ambient group containing the pair, with centralizing elements taken in the ambient group.
  locally-residually-finite-targets-kill-compression-defects: that kills the defect of an arbitrary compression in every homomorphism to a locally residually finite target, with no property (T); this kills rigid defects inside sofic source groups and needs property (T) of both the compressed group and the compressor group.
  compression-defect-dies-in-finite-dimensions: that kills the defect in finite-dimensional linear representations by commutant dimension, with no property (T); this is the normalized-Hamming statement, where no dimension is available and property (T) of both groups is necessary.
  one-sided-compression-nonsofic-criterion: that is the formalized OpenAI bridge concluding nonsoficity from a non-LEF commuting factor through one selected expander; this is the defect criterion, which implies the stronger conclusion that the conjugated commuting factor is central.
artifacts:
  - research/artifacts/rigid-compression-defect-ladder-2026-09-11.md
  - research/artifacts/kun-thom-2608-06222-verified.md
---

**ESTABLISHED.** Let `H` be a countable sofic group, and let
`Gamma <= G <= H` with `Gamma` and `G` Kazhdan and `Gamma` infranormal in `G`.
Then

```text
[g z g^-1, gamma] = 1     for all g in G, z in C_H(Gamma), gamma in Gamma.
```

Equivalently: a group with a nontrivial rigid compression defect is not
sofic. This is `DD(sofic)` in `rigid-compression-defect-normalization-dichotomy`.

## Consequences

- **Kun--Thom Theorem A.** `kun-thom-wreath-carries-rigid-defect` exhibits a
  nontrivial rigid defect in the coset wreath.
- **Kun--Thom Theorem B.** Take `H = G`: `C_G(Gamma)` is normal in `G`.
- **The OpenAI criterion, with a stronger conclusion.**
  `openai-criterion-commuting-factor-is-central`: the conjugated commuting
  factor lies in the center of `Gamma`, so it is abelian.
- **Free-lamp amalgams.** Every weak MF amalgam `G *_Gamma (Gamma x K)` over
  the Theorem E pair is nonsofic (`weak-mf-groups-can-carry-rigid-defects`).
- **Win--win on the hyperlinear side.** A hyperlinear group with a nontrivial
  rigid defect is nonsofic, which is the Q3.4 branch of
  `hyperlinear-groups-kill-rigid-compression-defects`.

## Sharpness

Property (T) of the compressor group cannot be dropped. The literal finitely
presented group `E` is sofic and carries a nontrivial compression defect of a
Kazhdan subgroup (`compressor-kazhdan-hypothesis-necessary-for-sofic-defects`).

Derivation: `sofic-rigid-defects-via-kun-thom-normalization`.
