---
rg: 2
id: fpbs-sparse-reuse-signal-near-cost-one
kind: claim
title: Near cost one the reuse signal can be made rare without becoming removable
artifacts:
  - research/artifacts/fpbs/docs/fixed-price-reuse-localization.md
  - research/artifacts/fpbs/responses/55_0909-215618.md
---

Run the localization theorem relative to a lifted aperiodic hyperfinite spine. For every epsilon > 0 there is an intermediate finite-observable factor Z with C(Z) < C(Y) + epsilon whose reuse flags satisfy sum_j nu(B_j) < C(Y) - 1 + epsilon, because each flag sits inside the used domain of its added edge and the relative budget is below C(Y) - 1 + epsilon. When C(Y) = 1 the whole signal is nontrivial on a set of measure below epsilon while the factor still has cost below 1 + epsilon.

Rarity is not removability. A rare connector may be reused by many requests, which is exactly the saving that cost measures. Quantitatively, if C(Y) = 1, C(X) = 1 + Delta, a relative plan has budget b and all its added-edge traffic is bounded by K, then J_pi <= (K-1)b and Delta <= b + J_pi <= Kb, so a positive gap would force K at least Delta/b as the relative budget shrinks. No uniform traffic bound is proved, so this is a constraint on any hypothetical gap, not a contradiction; small domain measure can conceal a large amount of shared work, and the plans change as they approach optimal cost.

Status records a written deduction, not independent validation.
