---
rg: 2
id: odd-measure-crossed-product-carries-mod-three-trace
kind: claim
title: The odd-measure crossed product over F_3 carries an invariant mod-three average and trace that separates some idempotents but not the corner target
artifacts:
  - research/artifacts/ternary-lift-signed-thompson-crossed-product-2026-09-12.md
---

Let `B = C(M_-, F_3) ⋊ V` be the signed Thompson subalgebra of the anti-central summand
(`signed-thompson-algebra-is-odd-measure-crossed-product`).

1. For a function `f` depending on `mu` through a finite clopen partition `P`, the average
   `tau(f) = 2^-(|P| - 1) . sum over odd vectors v in F_2^P of f(v)`, computed in `F_3`, is
   independent of `P`. It is `V`-invariant and has `tau(1) = 1`.
2. `Tr(sum_g f_g [g]) = tau(f_1)` is an `F_3`-valued trace on `B`, so equivalent idempotents have
   equal `Tr`.
3. `Tr(eps_-) = 1`, `Tr(q_[0]) = -1` and `Tr(q_[0] q_[00]) = 1`.
   * So `q_[0]` is not equivalent to its clopen subidempotent `q_[0] q_[00]`.
   * But `Tr` does not obstruct `eps_- <= q_[0]`: an equivalent subidempotent `e'` would have
     `Tr(e') = 1` and `Tr(q_[0] - e') = 1`, with no contradiction.

This is the mod-3 shadow of the real Haar measure of
`odd-measure-space-has-no-honest-thompson-compression`. It sees multiplicities mod 3 but carries no
order. Proposition 5 of the artifact.
