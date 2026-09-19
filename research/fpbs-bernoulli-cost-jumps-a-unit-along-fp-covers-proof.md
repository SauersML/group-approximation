---
rg: 2
id: fpbs-bernoulli-cost-jumps-a-unit-along-fp-covers-proof
kind: route
title: Baumslag truncations as HNN extensions, Britton for the commuting relator, and Gaboriau amalgam cost over Z
target: fpbs-bernoulli-cost-jumps-a-unit-along-fp-covers
requires:
  - fpbs-bernoulli-cost-usc-on-marked-groups
artifacts:
  - research/artifacts/fpbs-marked-group-cost-limits-2026-09-19.md
---

Artifact, Section 2, (B1) to (B5) and Corollary B'.

- **Convergence (B1).** Every element of `N_H` uses finitely many Baumslag relators.
- **HNN structure (B2).** Eliminate `a_i = t^i a t^-i`.
- **Infinite order (B3).** `r_R = a_0 t a_R t^-1 a_0^-1 t a_R^-1 t^-1`. It has no pinch, since `a_R` is not in
  `<a_0..a_(R-1)>` and `a_0` is not in `<a_1..a_R>`.
- **Cost (B5).** Use the Gaboriau amalgam and HNN cost bounds over infinite amenable subgroups (Invent. Math. 139,
  2000, IV.15 and IV.22), Ornstein-Weiss for the amenable pieces, and the Gaboriau inequality `beta_1 <= C - 1`.
- **The limit `H`.** Free-product additivity of cost and `beta_1`.
- **Corollary B'.** Uses Step 1 of the imported semicontinuity lemma.

Status records a written deduction over cited theorems, not formal verification.
