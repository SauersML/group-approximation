---
rg: 2
id: fpbs-pu-open-certificates-pinned-at-pc-proof
kind: route
title: Derived-series towers, relative Burton–Keane on the amenable approximants, and Easo–Hutchcroft locality
target: fpbs-pu-open-certificates-pinned-at-pc
requires:
  - fpbs-easo-hutchcroft-pc-locality
  - fpbs-hp-relative-burton-keane
  - fpbs-cluster-count-trichotomy
artifacts:
  - research/artifacts/fpbs-pu-nonlocality-2026-09-17.md
---

The complete proof is in the artifact, Sections 2–6.

1. **Lemma 1 (lifted exploration).** A marked surjection that induces a covering
   of Cayley graphs gives stochastic domination of the cluster size, so
   `p_c(S_k) <= p_c(Z^2) = 1/2`.
2. **Convergence.** `S_k -> F_2`, because `F^(k) <= gamma_(2^k)` and the lower
   central series of `F_2` intersects trivially.
3. **Relative Burton–Keane with `H = Gamma` amenable** gives
   `p_u(S_k) = p_c(S_k)`.
4. **Easo–Hutchcroft locality.** Its hypothesis `p_c(S_k) != 1` holds by step 1,
   so `p_u(S_k) -> 1/3`. On the tree, `p_u = 1` by the Newman–Schulman
   trichotomy.
5. **Theorem B.** Openness gives a ball `N_r(G)` and a window of width `eta`.
   An amenable approximant in `N_r(G)` with `p_c < p - eta` violates soundness
   at `p - eta/2`.
6. **Corollary C.** Harris gives `lambda = 1` under uniqueness, and a Chernoff
   bound on the tree gives `lambda(F_2,q) < 1`.
