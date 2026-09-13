---
rg: 2
id: subexponential-growth-simple-algebras-rank-model-proof
kind: route
target: subexponential-growth-simple-algebras-have-rank-models
requires:
  - simple-amenable-affine-algebras-have-unital-rank-models
  - elek-amenable-algebras-almost-have-fd-representations
artifacts:
  - research/artifacts/un-open-4-amenable-rank-models-2026-09-13.md
title: Proof — subexponential growth gives amenability (Elek), then apply the rank model theorem
---

Elek's Proposition 4.1 in arXiv:math/0203261 states that any affine algebra of subexponential growth is
amenable; it is imported as (E4) of `elek-amenable-algebras-almost-have-fd-representations`. Elek's proof
picks a subsequence `d_(m_n + n) ≤ d_(m_n)(1 + 2^{-n})` of ball dimensions, which exists whenever
`d_m ≤ C_ε (1+ε)^m` for every `ε > 0`, and takes the balls `R_(m_n)` as the Følner exhaustion.

Feeding that into `simple-amenable-affine-algebras-have-unital-rank-models` gives the unital rank model.
Details in §3 of the artifact.
