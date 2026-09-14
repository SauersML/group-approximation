---
rg: 2
id: sofic-rigid-defects-via-kun-thom-normalization
kind: route
title: Restrict an injective sofic representation of the ambient group to the pair and apply Kun--Thom normalization
target: sofic-groups-kill-rigid-compression-defects
requires: [kun-thom-sofic-centralizer-normalization, rigid-compression-defect-normalization-dichotomy]
artifacts:
  - research/artifacts/rigid-compression-defect-ladder-2026-09-11.md
---

1. Choose an injective sofic representation `rho : H -> S_U` with canonical
   trace.
2. Its restriction to `G` is an injective sofic representation of the
   infranormal Kazhdan pair, which is Theorem 4.1's hypothesis under any
   reading of "sofic representation".
3. Theorem 4.1 puts `rho(g) rho(z) rho(g)^-1` in `C_(S_U)(rho(Gamma))` for
   every `z in C_H(Gamma)`.
4. So `rho` kills `[g z g^-1, gamma]`, and injectivity kills it in `H`.

This is the `NORM => DD` half of the dichotomy, for the sofic class; see
Section 3 of the artifact.
