---
rg: 2
id: every-artin-dead-cut-admits-a-nonzero-dead-edge-ring
kind: claim
title: "Refuted approach: every disconnected living subgraph of an Artin group admits a nonzero dead-edge ring"
refuted_by: [artin-k4-dead-cut-admits-no-nonzero-dead-edge-ring]
---

Statement (refuted). For every Artin group `A_Γ` and every discrete `χ` with `Liv_0^χ`
connected and dominant and `Liv^χ` disconnected, there are:

- a vertex partition `V_1 ⊔ V_2` with live vertices on both sides and only dead cross
  edges;
- a nonzero ring `R` and `ρ : A_Γ -> R^×` killing every cross dead-edge sum
  `1 + ρ(uv) + ... + ρ(uv)^{l(e)/2 - 1}`.

If true, this would prove the Σ¹-conjecture through
`artin-sigma1-dead-edge-ring-obstruction`.

## Attempts

- 2026-09-13: refuted by the four-vertex graph `K` with cross labels `4, 4, 4, 6`
  (`artin-k4-dead-cut-admits-no-nonzero-dead-edge-ring`). The route
  `artin-sigma1-conjecture-via-dead-edge-rings` is therefore dead. Surviving
  generalization: module witnesses (artifact §4, Remark ii).
