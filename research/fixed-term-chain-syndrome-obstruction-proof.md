---
rg: 2
id: fixed-term-chain-syndrome-obstruction-proof
kind: route
title: Combine a slowly varying product state with uniform finite-patch spectral bounds and deficient range coverage
target: fixed-term-chain-defeats-bounded-syndrome-neighborhoods
requires: [range-cover-deficit-certifies-no-finite-syndrome-cost]
artifacts:
  - research/artifacts/qpcp-fixed-term-chain-2026-09-07.md
---

Sections 2 through 4 of the artifact provide the full all-size proof.
Swap invariance plus opposite endpoint penalties proves frustration;
deleting any one term gives a satisfying product state. A rational
interpolating product state has total energy at most `2/(n-1)`.
Every at-most-`L` term subset decomposes into short paths with at most one
pin per component. Permutation averaging and transport of the pinned
field prove the explicit positive spectral bound `delta_L`.
Occurrence then bounds total range mass by
`16R(L+1)^4/(n-1)<1`, so the prerequisite supplies a direct dual
certificate against every finite local charge constant.
