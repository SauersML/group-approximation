---
rg: 2
id: fpbs-fibre-bubble-forces-mean-field-susceptibility-proof
kind: route
title: Count supported fibres, then run Hutchcroft's differential inequality on lifted halfspaces
target: fpbs-fibre-bubble-forces-mean-field-susceptibility
requires: []
artifacts:
  - research/artifacts/fpbs/docs/fibre-summed-hyperbolic-quotient-criterion.md
---

Theorem 2.1 of the artifact, in three steps.

1. **Lemma 2.2.** Split the cluster's fibres into heavy (`m(q) >= 2B`) and
   light. Mass transport gives `E sum_q m(q)^2 = E[|K_o||K_o ∩ H|]`, and the
   tree-graph inequality bounds this by `chi_p B`. Hence `E|pi(K_o)| >= chi_p/(4B)`.
2. **Lemma 2.3.** The supporting-hyperplane theorem on `Q` (Hutchcroft
   arXiv:1804.10191 Corollary 4.3) supports at least half of the fibres of
   `pi(K)`. Mass transport and a union bound over the finitely many roots within
   distance `r` then give `E[|K_o| 1{pi(K_o) ⊆ H_Q(1,b)}] >= chi_p/(8BN_r)`.
3. **Proposition 5.1.** Take a translate of the lifted halfspace at distance
   at least 2 (proof of Hutchcroft Lemma 3.6). This makes the two clusters
   independent. Add the finite-energy step and Russo's formula to get
   `d^+chi_p/dp >= C^(-1) chi_p^2` on `[p_c/2,p_c)`, then integrate.
