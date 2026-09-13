---
rg: 2
id: l2-acyclic-stabilizers-spectral-sequence-proof
kind: route
title: Run the stabilizer spectral sequence with coefficients in N(G) and count dimensions
target: l2-betti-numbers-vanish-for-actions-with-l2-acyclic-stabilizers
requires: [lueck-dimension-additivity-cofinality-and-induction]
artifacts:
  - research/artifacts/leavitt-unit-l2-acyclicity-2026-09-12.md
---

Artifact Sections 3 and 4.
1. **Double complex.** `D_(t,p) = N(G) ⊗_(ZG) (P_t ⊗ C_p(X))`, with `P_* -> Z` a projective
   resolution and diagonal action.
2. **Filtration by `p`.** By Shapiro's lemma, `E^1_(p,t) = ⊕_[σ] H_t(G_σ; N(G))`.
3. **Filtration by `t`.** Rows `1 <= p <= m` vanish because `N(G)` is flat over `Z` and
   `H_p(X) = 0`. Row `0` gives `H_t(G; N(G))`. So `H_n(Tot) ≅ H_n(G; N(G))` for `n <= m`.
4. **Dimensions.** `dim_(N(G)) H_t(G_σ; N(G)) = β_t^(2)(G_σ) = 0` for `p + t <= m`, by flat
   induction. Countable sums, subquotients, and a finite filtration keep dimension zero, by
   additivity and cofinality.
