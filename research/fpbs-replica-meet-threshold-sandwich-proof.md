---
rg: 2
id: fpbs-replica-meet-threshold-sandwich-proof
kind: route
title: Take expectations by Tonelli, embed the cluster of the edgewise minimum, and apply the invariant-finite-set lemma to the intersection of unique infinite clusters
target: fpbs-replica-meet-threshold-sandwich
requires:
  - fpbs-cluster-count-trichotomy
artifacts:
  - research/artifacts/fpbs/docs/replica-meet-threshold-2026-09-18.md
---

The complete proof is in Section 1 of the artifact. Apart from the import
`fpbs-cluster-count-trichotomy` (used in item 3 only), it uses only Tonelli,
independence, the monotone coupling and Galton–Watson extinction.

1. **Mean.** `E|M_k(o)| = sum_x prod_i P(x in K^i(o)) = Z_k(p)`.
2. **Thinned cluster.** `omega_1 ∧ ... ∧ omega_k` is Bernoulli(`p^k`), and its
   open paths are open in every replica.
3. **Uniqueness.**
   - Lemma 1.1: if `S` is a random set with transitive-invariant law, then
     `n P(|S| = n) = |V| P(o in S, |S| = n)`. So `P(o in S, |S| < infinity) = 0`.
   - Apply it to `S = I^1 ∩ ... ∩ I^k` for `p > p_u`, where the `I^i` are the
     unique infinite clusters, and note `M_k(o) = S` on `{o in S}`.
4. **Hierarchy.** `M_(k+1) ⊆ M_k`.
5. **Trees.** Paths are unique, so `M_k(o) = K_(∧omega_i)(o)`. A critical
   binomial Galton–Watson tree dies out.
