---
rg: 2
id: nonsofic-groups-have-cluster-soficity-threshold-in-pc-pu-proof
kind: route
title: Monotone coupling, finite classes below p_c, and inherited nonsoficity above p_u
target: nonsofic-groups-have-cluster-soficity-threshold-in-pc-pu
requires:
  - uniqueness-phase-cluster-relations-inherit-nonsoficity
  - fpbs-critical-no-infinite-cluster
artifacts:
  - research/artifacts/percolation-soficity-threshold-2026-09-12.md
---

Proof in Section 3 of the artifact (Theorem 3.1), from Lemmas 1.1 and 1.5 of Section 1.

1. **Down-set.** For `p' <= p`, the cluster of `1` at `p'` is contained in the cluster at `p` for the same
   `xi`. So `R_(p') ⊆ R_p` on the same space. A subrelation of a sofic relation is sofic: restrict the
   embedding of `L(R_p)` to `L(R_(p'))`, which contains `L^inf(Omega)`, and note `[R_(p')] ⊆ [R_p]`
   (artifact Lemma 1.1).
2. **Below `p_c`.** For `p < p_c`, `theta(p) = 0`, so every cluster is finite a.s. At `p = p_c` the same
   holds on nonamenable Cayley graphs by `fpbs-critical-no-infinite-cluster`. A relation with finite
   classes is `⊔_n T_n x {n points}`. Its algebra is `⊕ L^inf(T_n) ⊗ M_n` and its full group consists of
   measurable fiberwise permutations, which embed with diagonal into diagonal and permutations into
   permutations (artifact Lemma 1.5).
3. **Above `p_u`.** `uniqueness-phase-cluster-relations-inherit-nonsoficity`.

The hyperlinear version uses the same three steps with embeddings into `R^omega`.
