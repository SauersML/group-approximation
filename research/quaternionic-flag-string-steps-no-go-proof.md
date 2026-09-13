---
rg: 2
id: quaternionic-flag-string-steps-no-go-proof
kind: route
title: Zero defect forces k_i + p·d_i constant, a nonzero count forces some d_i = 0, and then the dimension equation reads sum k_i^2 = −m^2
target: quaternionic-flag-trapping-steps-are-never-string
requires: []
---

Put x_i = c_2(zeta_i). Here (+)_i zeta_i = H^n is trivial, and every c_1
vanishes. In degree four, the only relation in H^*(F; Z) is sum_i x_i = 0,
and H^4(F; Z) is torsion-free with rank s − 1 (Borel's presentation
Z[q(zeta_1), ..., q(zeta_s)]/(prod_i q(zeta_i) = 1)).

*Tangent.* TF ≅ (+)_{i<j} Hom_H(zeta_i, zeta_j). For quaternionic A, B of ranks
a, b, we have Hom_H(A, B) (x)_R C ≅ A* (x)_C B, so
lambda(Hom_H(A, B)) = −(b·c_2(A) + a·c_2(B)). Summing,
lambda(TF) = −sum_i (n − k_i)·x_i = sum_i k_i·x_i.

*Detector bundle.* W_R = p·Q_R, so lambda(W_R) = p·p_1(Q_R)/2 =
−p·sum_i d_i·x_i. The defect is sum_i (k_i + p·d_i)·x_i. It vanishes if and
only if k_i + p·d_i = t is independent of i.

*Count.* e(W_R) = c_top(Q)^p = prod_i c_{2k_i}(zeta_i)^{p·d_i}. If every
d_i >= 1, this contains prod_i c_{2k_i}(zeta_i) = c_{2n}(H^n) = 0. So some
d_s = 0, and then k_s = t.

*Dimension.* dim_R F = 4·sum_{i<j} k_i k_j = 2(n^2 − sum k_i^2).
rank_R W = 4p·sum_i k_i d_i = 4·sum_i k_i (t − k_i) = 4(tn − sum k_i^2).
Equality gives sum_i k_i^2 = n(2t − n). Put t = k_s and
m = n − t = sum_{i != s} k_i >= 1. Then the right side is
(t + m)(t − m) = t^2 − m^2, while the left side is t^2 + sum_{i != s} k_i^2. So
sum_{i != s} k_i^2 = −m^2 < 0, which is impossible. □

Check: s = 2 is the Grassmannian. There the defect is k·q_1 (with d_2 = 0,
t = k_2), consistent with quaternionic-grassmannian-trapping-defect-is-rank.
