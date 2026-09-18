---
rg: 2
id: smooth-design-rich-2to1-via-branch-selector
kind: route
title: Pad the orientation lift of the proved 2-to-1 instances with an equality coordinate and right-merge, giving admissible all-pairings laws at every alphabet size
target: smooth-design-rich-2to1-hardness
requires: [two-to-two-games-theorem, orientation-lifts-sandwich-2to1-game-values, efficient-branch-selector-on-proved-2to1-instances]
---

This links the branch-selector hole to the pairing-law ladder. With
`finite-moment-hardness-from-smooth-design` it also feeds
`finite-moment-pairing-2to1-hardness`.

Fix `epsilon`, `t`, `m`, `K` and `n_0`.

1. **Selector.** Choose `eta <= epsilon/2` with `eta'(eta) <= epsilon`. Let `o` be
   the selector of `efficient-branch-selector-on-proved-2to1-instances` for
   `R_eta`, and let `U = U_o(R_eta(x))` be the lift, with alphabet `[2k_0]`. By
   the selector claim, YES gives `val(U) >= 1 - epsilon`. By item (1) of
   `orientation-lifts-sandwich-2to1-game-values` and `two-to-two-games-theorem`,
   NO gives `val(U) <= val(R_eta(x)) <= eta <= epsilon/2`.
2. **Equality padding.** This is the step of `smooth-design-rich-2to1-from-ugc`.
   Replace the alphabet by `[2k_0] x [r]` and each bijection `phi` by `phi x id`.
   The value is exactly preserved: constant second coordinates keep a
   labelling's value, and projecting to the first coordinate never loses. Choose
   `r` even with `k_0 r >= max(n_0, t)`, and large enough for BKM Lemma 4.2 at
   `(K, m)` (ECCC TR19-141). This is the same import used by
   `smooth-design-rich-2to1-from-ugc`.
3. **Right merge.** Apply `Psi` at alphabet `2k = 2 k_0 r`. By item (2) of the
   sandwich (equivalently, BKM Appendix B), the output is fully rich and
   `val <= 2 val(U)`. So YES gives `>= 1 - epsilon` and NO gives `<= epsilon`.
   Its size is polynomial because `k` is a constant.
4. **Admissible.** The law at every left vertex is uniform on all pairings of
   `[2k]`. It is `t`-wise uniform for `t <= k`. It is `(K, m, C(K, m))`-smooth for
   large `k` by BKM Lemma 4.2, as in step 4 of `smooth-design-rich-2to1-from-ugc`.

So `Gap-2-to-1_k[1 - epsilon, epsilon]` is NP-hard on admissible instances at
`k >= n_0`. That is the hypothesis `smooth-design-rich-2to1-hardness` at
`(epsilon, t, m, K)`.

Unlike `smooth-design-rich-2to1-from-ugc`, this route does not assume UG hardness.
The unique game it merges is the lift of the proved instances. Its single open
input is the branch selector on those instances, a statement about the fixed
Grassmann family only. `square` (modulo the open
prerequisite)
