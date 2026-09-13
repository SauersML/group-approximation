---
rg: 2
id: coarse-frame-normalizers-are-near-block-monomial-proof
kind: route
title: The block transition matrix is doubly stochastic; random signs make it near a permutation, and polar parts give the blocks
target: coarse-frame-normalizers-are-near-block-monomial
requires: []
artifacts:
  - research/artifacts/ex-q34-imprimitivity-witness-2026-09-12.md
---

Complete proof in the artifact, section 1.

Put `A_ji = Tr(p_j u p_i u^*)/k`, a doubly stochastic matrix.  For
`f = sum_i f_i p_i`, `E_B(u f u^*) = sum_j (A f)_j p_j`, and the defect squared
is `||f||_2^2 - (1/n) ||A f||^2`.  Averaging over random signs gives
`(1/n) sum_i max_j A_ji >= 1 - delta^2`.  The argmax map is injective where
the max exceeds `1/2`, and the remaining indices have density `<= 2 delta^2`.
Extending to a permutation `sigma` gives
`||u - sum_i p_(sigma(i)) u p_i||_2^2 = (1/n) sum_i (1 - A_(sigma(i) i)) <= 3 delta^2`,
because the columns `(1 - p_(sigma(i))) u p_i` are HS-orthogonal.  Each block
`b_i = p_(sigma(i)) u p_i` is a contraction with polar unitary `w_i`, and
`Tr((1 - |b_i|)^2) <= Tr(1 - |b_i|^2) = k (1 - A_(sigma(i) i))`.  Adding the two
errors gives `2 sqrt(3) delta`.

For products, write `v f v^* = E_B(v f v^*) + e_v`, apply `u` to the conditional
expectation (an element of the unit ball of `B`), and use that the distance to
`B` is at most the distance to any element of `B`.  The perturbation bound
uses `||u' f u'^* - u f u^*||_2 <= 2 ||u - u'||_2`.
