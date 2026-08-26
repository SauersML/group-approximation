---
rg: 2
id: atlas-first-disjoint-mixed-pair-zero-rank-proof
kind: route
title: Evaluate the first distinct-source pair on four rectangular root objects
target: atlas-first-disjoint-mixed-pair-has-zero-reservoir-rank
requires: []
---

The MSI replay gives entries `380,381` and their exact sparse word sizes.
For the mathematical proof, set `N=iota_1ap_2` and
`M_j=iota_4b_jp_3`. The four root indices are disjoint in the sense needed
for St2, so `NM_j=M_jN=0`. Hence the pair of commutators is identically one
for arbitrary coefficient maps.

A positive nuisance-quotient rank would bound a chosen nonzero function of
`b_0,b_1` by these identically zero residuals, contradicting the rectangular
model. This proves rank increment zero and invalidates the proposed route.
