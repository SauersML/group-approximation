---
rg: 2
id: fpbs-meet-threshold-capped-by-amenable-relative-threshold-proof
kind: route
title: Intersect the unique H-infinite clusters of the k replicas and apply the invariant-finite-set lemma inside H
target: fpbs-meet-threshold-capped-by-amenable-relative-threshold
requires:
  - fpbs-hp-relative-burton-keane
  - fpbs-cluster-count-trichotomy
  - fpbs-relative-gap-along-any-subgroup-separates
artifacts:
  - research/artifacts/fpbs/docs/replica-meet-amenable-caps-2026-09-19.md
---

The complete proof is in Sections 0, 1.1, 1.2 and 3 (Corollary C) of the
artifact.

1. **Lemma 0.** An `H`-invariant random subset `W` of an infinite group `H` is
   a.s. infinite on `{h in W}`. The proof sums `P(h in W, |W| = n)` over `h`.
2. **Item 1.** `H` acts on the edges with finite stabilisers, so Bernoulli is
   `H`-ergodic.
   - For `p > p_c(H;G)`, an `H`-infinite cluster exists a.s.
   - By relative Burton–Keane (`fpbs-hp-relative-burton-keane`) it is unique;
     call it `U_i`.
   - `P(o in U_i) > 0` by invariance.
   - `W = ∩_i U_i ∩ H` has `H`-invariant law and `P(o in W) > 0`.
   - `W ⊆ M_k(o)` on `{o in W}`, and `W` is infinite there by Lemma 0.
3. **Item 2.** The same argument inside `Y`, with the unique infinite cluster
   of `Y` for `p > p_u(Y)` (`fpbs-cluster-count-trichotomy` item 2). Also
   `Y ⊆ G` gives `p_c(H;G) <= p_c(Y)`.
4. **Item 3.** `p_c(G) < p <= p_cap^(k)` together with items 1 and 2. The
   finite-mean form comes from `fpbs-relative-gap-along-any-subgroup-separates`
   (1 ⇔ 2).
