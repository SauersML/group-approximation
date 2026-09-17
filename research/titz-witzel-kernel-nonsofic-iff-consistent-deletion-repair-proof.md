---
rg: 2
id: titz-witzel-kernel-nonsofic-iff-consistent-deletion-repair-proof
kind: route
title: Common fixed points give deletion repair from collapse, Kazhdan rounding gives collapse from repair, and the simple-group limit kernel links collapse to nonsoficity
target: titz-witzel-kernel-nonsofic-iff-consistent-deletion-repair
requires:
  - kazhdan-consistent-partial-models-round-to-finite-actions
  - kazhdan-sofic-models-carry-long-scale-monodromy
  - infinite-simple-group-permutation-stable-iff-nonsofic
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
---

# Proof

**Inputs on `K`.** By `titz-witzel-simple-kazhdan-cat0-lattices-exist`, `K` is a finite-index
subgroup of a finitely presented group, so it is finitely presented. It is infinite, simple and
Kazhdan, so every finite generating set has a Kazhdan constant. An infinite simple group has no
nontrivial finite quotient. The presentation `<S | R>` is over the alphabet `S` (letters and their
formal inverses), so the kernel of `F(S) -> K` is the normal closure of `R`. Write `d = d_H`, a
bi-invariant metric.

## 1. Item 1

This is item 1 of `kazhdan-consistent-partial-models-round-to-finite-actions`, applied to the best
consistent set.

## 2. Item 2

**(a) => (d).** Let `sigma_j` be an almost solution. For each `g in K` fix a word `w_g`, and put
`phi_j(g) = sigma_j(w_g)`.
* For `g, h in K`, the word `u = w_(gh)^(-1) w_g w_h` is trivial in `K`. So in `F(S)` it is a fixed
  finite product of conjugates of `r^(±1)`, `r in R`.
* By bi-invariance, `d(phi_j(gh), phi_j(g)phi_j(h)) = d(sigma_j(u), 1)`. This is at most the sum
  of the corresponding `d(sigma_j(r), 1)`, which tends to 0.

So `phi_j` is an almost homomorphism in the sense of `infinite-simple-group-permutation-stable-iff-nonsofic`.
`K` is infinite, simple and not sofic, so (1 => 2) there gives `d(phi_j(g), 1) -> 0` for every
`g`. For a word `w` with value `g`, the word `w_g^(-1) w` is trivial, and in the same way
`d(sigma_j(w), phi_j(g)) = d(sigma_j(w_g^(-1)w), 1) -> 0`. Hence `d(sigma_j(w), 1) -> 0`.

**(d) => (c).** Take `w = s`.

**(c) => (b).** Let `A_j` be the set of common fixed points of the `sigma_j(s)`, `s in S`. Then
`|[n_j] \ A_j| <= sum_s d(sigma_j(s),1) n_j = o(n_j)`. A path starting at a common fixed point
never moves, whichever letters it reads, so it closes. Hence `A_j` is consistent and
`eta(sigma_j) -> 0`.

**(b) => (c).** This is (DR1).

**(c) => (a).** Suppose `K` is sofic, and let `psi_j : K -> Sym(n_j)` satisfy
`d(psi_j(gh), psi_j(g)psi_j(h)) -> 0` for all `g, h` and `d(psi_j(g), 1) -> 1` for all `g != 1`.
Put `sigma_j(s) = psi_j([s])`.
* From `d(psi_j(1), psi_j(1)^2) -> 0` we get `d(psi_j(1), 1) -> 0`. From
  `d(psi_j(1), psi_j(g)psi_j(g^(-1))) -> 0` we get `d(psi_j(g)^(-1), psi_j(g^(-1))) -> 0`.
* For `r = l_1...l_k`, the triangle inequality along prefixes then gives
  `d(sigma_j(r), psi_j([r])) -> 0`. Since `[r] = 1`, this gives `d(sigma_j(r), 1) -> 0`, so
  `sigma_j` is an almost solution.
* `K` is nontrivial, so some `s in S` has `[s] != 1`. Then `d(sigma_j(s), 1) -> 1`, contradicting
  (c).

## 3. Item 3

The negation of (b) is an almost solution with `limsup eta(sigma_j) > 0`. Passing to a
subsequence gives `liminf > 0`. Conversely, if `K` is sofic, the almost solution built in
(c) => (a) has mark tending to 1, and by (DR1) its deficit is at least `c_kappa m`. The filling
radius statement is item 2 of `kazhdan-sofic-models-carry-long-scale-monodromy`, with
`eps_j = 2 sum_r |r| d(sigma_j(r),1) -> 0`.

## 4. The remarks on (P2)

The Folner remark is the calibration of `kazhdan-consistent-partial-models-round-to-finite-actions`.
Deleting the `R_0`-neighbourhood of the bad set is the set `A` of step 3 of
`kazhdan-sofic-models-carry-long-scale-monodromy-proof`, which is not consistent under (LS1).
