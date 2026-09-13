---
rg: 2
id: quaternionic-grassmannian-trapping-defect-proof
kind: route
title: Schubert calculus doubles from Gr_k(C^n), and TG (+) End_H(zeta) = Hom_H(zeta, H^n) gives the Pontryagin classes
target: quaternionic-grassmannian-trapping-defect-is-rank
requires: []
artifacts:
  - research/artifacts/class-four-lambda-mod-eight-trapping-part2-2026-09-13.md
---

Part 2, Lemmas 4.1 and 4.2.

Count. H^*(Gr_k(H^n); Z) has Borel's presentation
Z[q, q']/(q·q' = 1), the same as H^*(Gr_k(C^n); Z) with degrees doubled.
The top symplectic class q_k corresponds to sigma_{1^k}. Pieri's rule gives
sigma_{1^k}^{2d} = sigma_{(2d)^k} = [pt] on Gr_k(C^{k+2d}).

Defect. We have TG (+) Hom_H(zeta, zeta) ≅ Hom_H(zeta, H^n), and
Hom_H(A, B) (x)_R C ≅ Hom_C(A, B). With c_2(A* (x) B) = beta·c_2(A) +
alpha·c_2(B) for c_1 = 0, this gives p_1(TG) = −(2n − 4k)·q_1. Also
p_1(W_R) = −4d·q_1. H^4 is torsion-free, so lambda = p_1/2. With n = k + 2d,
the difference is k·q_1.

Check: k = 1 recovers p_1(HP^{2d}) = 2(2d − 1)·u, with u = −q_1.
