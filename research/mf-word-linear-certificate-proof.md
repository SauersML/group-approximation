---
rg: 2
id: mf-word-linear-certificate-proof
kind: route
title: Amplify a spectral phase with at most pi over its displacement tensor factors
target: mf-radical-words-have-linear-certificates
requires: []
artifacts:
  - research/artifacts/mf-word-linear-certificates.md
---

## Proof

The artifact proves all three implications. Corona compactness gives a
finite threshold below marked displacement one. For a unitary `A` with
`t=||A-I||>0`, choose an eigenvalue `e^(i theta)` attaining `t`, with
`0<|theta|<=pi`, and put `k=ceil(pi/(2|theta|))`. Then `k|theta|` lies in
`[pi/2, pi]`, so `|e^(i k theta)-1|=2|sin(k theta/2)|>=sqrt(2)>1`, and
`t=2|sin(theta/2)|<=|theta|` gives `k t <= k|theta| <= pi`, that is
`k <= pi/t`. This replaces the earlier geometric-series argument and
improves the constant from `6/t` to `pi/t`.
The same eigenvalue survives in `A^(tensor k)`. Tensoring all generator
matrices is a group homomorphism, so every relator defect grows by at most
`k`, while the selected word crosses the threshold. Consequently
`eta<=k delta<=pi delta/t`, giving the stated linear bound. Unitary lifts
of corona generators prove the converse. The artifact also gives the
finite-word union argument and the normal-closure cost for a fixed finite
presentation.

This is a complete direct written proof, with the spectral and compactness
steps included in the artifact. It is not a Lean certificate.
