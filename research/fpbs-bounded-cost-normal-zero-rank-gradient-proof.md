---
rg: 2
id: fpbs-bounded-cost-normal-zero-rank-gradient-proof
kind: route
title: Factor the profinite boundary action onto the completion of the quotient chain and apply the larger-kernel cost-one theorem
target: fpbs-bounded-cost-normal-unbounded-chain-zero-rank-gradient
requires:
  - fpbs-quotient-split-larger-kernel-cost-one
  - fpbs-abert-nikolov-rank-gradient-equals-profinite-cost
  - fpbs-small-marker-induction-input
artifacts:
  - research/artifacts/fpbs/normal-finite-cost-rank-gradient-2026-09-17.md
---

Written proof in Sections 3 and 4 of the linked note.

* **Corollary 3.1.** `lim G/G_n` factors onto `lim G/G_nN`. The kernel of that factor action is `M = ∩ G_nN`, and `G/M` acts freely with cost at most `d(G)`. Theorem A' gives cost one, and Abert--Nikolov Theorem 1 converts this into zero gradient.
* **Proposition 4.2.** Once `G_nN = M_0` has finite index `a`, the boundary space of `M_0` is `N`-isomorphic to `lim N/(N∩G_n)`. Normal subgroup monotonicity (Lemma 4.1, reproved from small markers and the normalizer trick) gives `1 + a·RG = C(R_{M_0}) ≤ C(R_N)`.

This is dependency bookkeeping for a written deduction, not a formal verification.
