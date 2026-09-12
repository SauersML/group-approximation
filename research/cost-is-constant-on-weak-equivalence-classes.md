---
rg: 2
id: cost-is-constant-on-weak-equivalence-classes
kind: claim
title: The cost of a free action is monotone under weak containment and constant on weak-equivalence classes
distinct_from:
  fpbs-bernoulli-maximal-cost: that is the consequence that Bernoulli actions have maximal cost among free actions; this is the monotonicity of cost under weak containment itself, from which constancy on weak-equivalence classes follows.
artifacts:
  - research/artifacts/weak-invariant-blindness-for-bernoulli-rokhlin-entropy-2026-09-12.md
---

**ESTABLISHED (import).** Let `G` be a countable group and let `a`, `b` be free p.m.p. actions of
`G`. If `b ≺ a`, then `C(a) ≤ C(b)`. So two weakly equivalent free actions have the same cost.

Source: Abért–Weiss, *Bernoulli actions are weakly contained in any free action*, arXiv:1103.1063,
Theorem 9. The repository already consumes this theorem in the body of
`fpbs-bernoulli-noise-does-not-change-cost-proof`. This node imports it as a claim, so routes can
require it.
