---
rg: 2
id: unbalanced-effective-rule-certifies-strictness-proof
kind: route
title: Left inverse gives injectivity; surjectivity would preserve the uniform measure and balance the effective rule
target: unbalanced-effective-rule-certifies-strictness
requires:
  - bijective-ca-preserve-uniform-bernoulli-measure
  - strict-automata-live-on-canonical-table-groups
artifacts:
  - research/artifacts/unbalanced-design-memory-collisions-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

The argument follows Proposition 1 and Corollary 2 of the artifact.

- **Injectivity.** By Lemmas 1 and 2 of the canonical-table artifact, a forward table `>= E` with
  `E` forward sufficient gives `sigma_rho tau_rho = id`.
- **Surjectivity would balance the rule.** If `tau_rho` were surjective it would be bijective, and
  it would preserve `lambda` by the first prerequisite. Its one-site marginal would then be uniform.
  That marginal is the effective rule applied to independent uniform symbols at the distinct points
  `rho(M)`, so the effective rule would be balanced.
- **Over the table group.** Lemma 5 of the canonical-table artifact says `rho_E` has forward table
  `>= E`, and its collision partition is that of the letters `x_m` in `U_E`.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS.** Re-derived independently: the one-site law at the
distinct points `rho(M)`, measure preservation of bijections, the sofic-quotient remark, and the `F_2`
top-coefficient criterion for robust unbalance
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 6).
