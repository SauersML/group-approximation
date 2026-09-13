---
rg: 2
id: sofic-action-with-sofic-ergodic-components-is-sofic
kind: claim
title: A p.m.p. action whose ergodic components are almost all sofic is sofic, so a group outside Paunescu's class has a free ergodic nonsofic action
distinct_from:
  sofic-action-class-closed-under-commensurability: that is permanence of Paunescu's class under subgroups and finite-index overgroups; this is permanence of soficity of one action under ergodic decomposition
  paunescu-sofic-action-class-permanence: that imports Theorem 3.1, reducing arbitrary actions to free ones; this reduces free actions to free ergodic ones
artifacts:
  - research/artifacts/nonsofic-action-mixing-transfer-2026-09-12.md
---

**ESTABLISHED.** Let `G` be a countable group and `G ↷ (X,μ)` a p.m.p. action with ergodic
decomposition `μ = ∫ μ_t dν(t)`. If for ν-almost every `t` the action `G ↷ (X,μ_t)` is sofic
(Păunescu Definition 1.4), then `G ↷ (X,μ)` is sofic.

Consequently, if `G` is not in Păunescu's class `𝒮`, then `G` has an essentially free, **ergodic**
p.m.p. action that is not sofic.

**Why it matters.** Every mixing and every Howe--Moore argument needs an ergodic seed. The
consequence turns "`G ∉ 𝒮`" into such a seed with no further input, for instance in
`howe-moore-lattice-nonsofic-action-transfers-to-mixing`.

Proof in `sofic-action-with-sofic-ergodic-components-is-sofic-proof`.
