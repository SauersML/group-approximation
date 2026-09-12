---
rg: 2
id: relative-defect-via-relative-normalization
kind: route
title: Normalize the relative centralizer modulo the Kazhdan kernel and read the defect through an injective sofic representation
target: sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels
requires:
  - relative-normalization-modulo-kazhdan-kernel
  - relative-defect-normalization-dichotomy
artifacts:
  - research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md
---

`relative-defect-normalization-dichotomy` proves `RNORM ==> RDD`. Its first
half, applied with the open premise `relative-normalization-modulo-kazhdan-kernel`:

1. Take an injective trace-zero sofic representation `sigma` of the sofic
   host `H`.
2. A relatively centralizing `z` gives `sigma(z) in N_rel(sigma|_G)`.
3. Normalization moves it by `sigma(g)`, so `sigma([g z g^-1, gamma])` lies in
   `sigma(M)`.
4. By injectivity, `[g z g^-1, gamma] in M`.

This replaces `relative-defect-via-normalizer-split`, whose splitting premise
is refuted. Unlike `relative-rigid-defect-from-kazhdan-quotient-permanence`,
it never assumes that `H/M` is sofic. Its premise is exactly equivalent to the
target, so it adds no strength; its value is the formulation. The whole
difficulty is concentrated in one ultraproduct statement. Its `M = 1` case
follows from Kun--Thom Theorem 4.1 together with the absolute
`rigid-compression-defect-normalization-dichotomy`.
