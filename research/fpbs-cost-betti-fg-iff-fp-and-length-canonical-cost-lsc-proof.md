---
rg: 2
id: fpbs-cost-betti-fg-iff-fp-and-length-canonical-cost-lsc-proof
kind: route
title: Squeeze Bernoulli cost between the Gaboriau bound and Pichot semicontinuity along the length-canonical covers
target: fpbs-cost-betti-fg-iff-fp-and-length-canonical-cost-lsc
requires:
  - fpbs-bernoulli-cost-usc-on-marked-groups
artifacts:
  - research/artifacts/fpbs-marked-group-cost-limits-2026-09-19.md
---

Artifact, Section 3, Theorem C.

- **Imports.** Pichot (Comment. Math. Helv. 81, 2006) for `limsup beta_1(G_n) <= beta_1(G)` on marked groups, and
  the Gaboriau inequality `C >= 1 + beta_1`.
- **Semicontinuity lemma.** It makes `SEL_len` equivalent to convergence of cost.
- **Each `G^_R` is infinite and finitely presented.** It surjects onto `G`, and `B_R` is finite.
- **Part (1).** The displayed chain of inequalities.
- **Part (2).** Substitute the equality at every term and at the limit.
- **Part (3).** Combine (1) and (2).

Status records a written deduction over cited theorems, not formal verification.
