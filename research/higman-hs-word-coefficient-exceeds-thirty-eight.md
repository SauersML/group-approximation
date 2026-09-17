---
rg: 2
id: higman-hs-word-coefficient-exceeds-thirty-eight
kind: claim
title: A rational six-dimensional Higman tuple rules out coefficient thirty-eight, while the trivial three-cycle already exceeds ten
distinct_from:
  higman-hs-word-coefficient-exceeds-sixteen: that refutes coefficient sixteen with a U(3) tuple; this refutes thirty-eight with a U(6) tuple and adds the matching calibration for the trivial Higman three-cycle.
  failed-hs-word-bounds-have-rational-witnesses: that semidecides failure of a specified coefficient; this supplies explicit Q(i) matrices and exact margins.
  higman-order-three-torsion-ratio-bound: that proves a finite coefficient on the order-three torsion class; this witness lies in that class, so it is certified nontrivial but cannot scale to infinity.
artifacts:
  - research/artifacts/higman-hs-ratio-scaling-scout-2026-09-17.md
  - experiments/higman-hs-microstate-scaling-2026-09-17/certify_ratio_witness.py
  - experiments/higman-hs-microstate-scaling-2026-09-17/ratio_witness_cycle4_d6.json
  - experiments/higman-hs-microstate-scaling-2026-09-17/ratio_witness_cycle3_d6.json
  - experiments/hs_word_certificate.py
---

Higman four-cycle, `r_j=g_j g_(j+1) g_j^(-1) g_(j+1)^(-2)`, `j in Z/4`. An
explicit rational U(6) tuple has `e(g_0)/sum_j e(r_j) = 38.7323... > 38`.
The tuple is four Cayley transforms of skew-Hermitian matrices with entries
in `Q(i)/1024`. So every dimension-free coefficient `C` in
`e(g_0)<=C sum_j e(r_j)` exceeds 38, above the previous 16.

Calibration. For the three-cycle `<g_0,g_1,g_2 | g_j g_(j+1) g_j^(-1)=g_(j+1)^2, j in Z/3>`,
which is the trivial group, an explicit rational U(6) tuple has ratio
`10.3213... > 10`. Its best coefficient is finite (van Kampen area) but
exceeds ten.

What it rules out. Coefficients at most 38 for Hig, and at most 10 for
the trivial three-cycle. A certified Higman coefficient of order 10 to 40
is therefore no evidence of a nontrivial hyperlinear quotient. The trivial
group already shows the same order of magnitude. The H4 tuple has odd
generators of exact order three, so by
higman-order-three-torsion-ratio-bound its class is bounded by 17973. No
all-dimensions upper bound for Hig and no existence conclusion is asserted.
