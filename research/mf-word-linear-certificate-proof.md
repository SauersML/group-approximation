---
rg: 2
id: mf-word-linear-certificate-proof
kind: route
title: Amplify a spectral phase with at most six over its displacement tensor factors
target: mf-radical-words-have-linear-certificates
requires: []
artifacts:
  - research/artifacts/mf-word-linear-certificates.md
---

## Proof

The artifact proves all three implications. Corona compactness gives a
finite threshold below marked displacement one. For a unitary `A` with
`t=||A-I||>0`, choose an eigenvalue `z` attaining `t`. The geometric-series
identity shows that some `1<=k<=floor(4/t)+1<=6/t` has `|z^k-1|>1`.
The same eigenvalue survives in `A^(tensor k)`. Tensoring all generator
matrices is a group homomorphism, so every relator defect grows by at most
`k`, while the selected word crosses the threshold. Consequently
`eta<=k delta<=6 delta/t`, giving the stated linear bound. Unitary lifts
of corona generators prove the converse. The artifact also gives the
finite-word union argument and the normal-closure cost for a fixed finite
presentation.

This is a complete direct written proof, with the spectral and compactness
steps included in the artifact. It is not a Lean certificate.
