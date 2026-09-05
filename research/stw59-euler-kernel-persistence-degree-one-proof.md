---
rg: 2
id: stw59-euler-kernel-persistence-degree-one-proof
kind: route
title: Preserve the integral Euler map under both actual connecting blocks and take its kernel through the limit
target: stw59-independent-component-and-degree-one-obstructions
requires:
  - stw59-exact-finite-abelian-unitary-component-groups
  - stw59-monotracial-matrix-stable-counterexamples
artifacts:
  - research/artifacts/stw59-persistent-euler-degree-one-cokernel-2026-09-05.md
---

The one-line gauge fibration identifies the image of the degree-one
stable map with the kernel of the integral relative Euler map.
For the rank-r tower step, Morita K0 sends a virtual bundle beta to
pull(beta)+rank(beta)[L], and the new bundle is pull(E)+L^r.

In the Euler formula the pullback summand contributes Lambda_E(beta)
times c1(L)^r. The evaluation-line summand contributes zero because
old top degree forces c_r(E), and E has a global trivial line.
Thus the actual connecting homomorphisms preserve the Z^s Euler
coordinates and their exact image direct sum_alpha d_alpha Z.

Finite-stage exactness and relative loop continuity identify the
image of pi_1 U(A) with the kernel of the limit Euler map. Its
cokernel is consequently Z^s, also after identifying the matrix-
size-two unitary group with stable K-theory. Rationalization leaves
cokernel Q^s.

The joined-base construction extends to d_alpha=1 using CP^0 and
one common trivial line. The Bott attaining class gives Euler image
Z on such an arm, contributing no component group and one free
degree-one obstruction. The existing simplicity, trace contraction,
and matrix stable-range proofs apply to these same-rank towers.
The nonzero degree-one cokernel rules out stable rank one by the
verified loop-surjectivity theorem; together with the homogeneous
upper bound, it gives stable rank exactly two for every example.
