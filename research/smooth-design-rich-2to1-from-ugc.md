---
rg: 2
id: smooth-design-rich-2to1-from-ugc
kind: route
title: Pad a hard unique game and apply BKM's uniform-pairing reduction, whose all-pairings families are admissible
target: smooth-design-rich-2to1-hardness
requires: [unique-games-conjecture]
---

The converse direction. SD-Rich is **equivalent** to UGC, not weaker than it.
Together with `ugc-from-smooth-design-rich-2to1` this is an equivalence cycle.
A least fixpoint establishes neither end. The cycle warning is expected and
must not be "fixed" by deleting either true implication.

Fix `epsilon`, `t`, `m`, `K` and `n_0`.

1. **UGC.** `Gap-Unique_q[1-epsilon/2, epsilon/2]` is NP-hard for some `q`.
2. **Equality padding.** Replace the alphabet by `[q] x [r]` and each constraint
   `Phi(u,v)` by `{((a,b),(a',b')) : (a,a') in Phi(u,v), b = b'}`. A labeling
   with constant second coordinate keeps its value, and no labeling beats its
   first coordinate. So the value is exactly preserved, and the alphabet becomes
   `qr`. Choose `r` even with `qr/2 >= max(n_0, t)` and large enough for BKM
   Lemma 4.2 at `(K,m)`.
3. **BKM Appendix B** (ECCC TR19-141), at alphabet `2k = qr`. Right vertices are
   `(v, sigma)` with `sigma` ranging over all 2-to-1 maps `[2k] -> [k]`, and the
   constraint on `(u,(v,sigma))` is `sigma o Phi(u,v)`. The instance has
   polynomial size, since `k` is constant. Completeness `1-epsilon/2` carries
   over. A labeling of value `delta` yields a unique-game labeling of value
   `delta/2`, so soundness `epsilon/2` gives `epsilon`.
4. **Admissible.** `Phi(u,v)` is a bijection and `sigma` is uniform, so the
   pairing of a random edge at `u` is uniform over all pairings of `[2k]`. That
   family is `t`-wise uniform for `t <= k` by definition, and
   `(K,m,C(K,m))`-smooth for large `k` by BKM Lemma 4.2.

So `Gap-2-to-1_k[1-epsilon, epsilon]` is NP-hard on admissible instances at
`k >= n_0`, which is the hypothesis `smooth-design-rich-2to1-hardness` at
`(epsilon, t, m, K)`.
