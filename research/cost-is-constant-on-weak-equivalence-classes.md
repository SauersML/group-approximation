---
rg: 2
id: cost-is-constant-on-weak-equivalence-classes
kind: claim
title: For a finitely generated group, the cost of a free action is monotone under weak containment and constant on weak-equivalence classes
distinct_from:
  fpbs-bernoulli-maximal-cost: that is the consequence that Bernoulli actions have maximal cost among free actions; this is the monotonicity of cost under weak containment itself, from which constancy on weak-equivalence classes follows.
artifacts:
  - research/artifacts/weak-invariant-blindness-for-bernoulli-rokhlin-entropy-2026-09-12.md
---

**ESTABLISHED (import).** Let `G` be a finitely generated group and let `a`, `b` be free p.m.p.
actions of `G`. If `b ≺ a`, then `C(a) ≤ C(b)`. So two weakly equivalent free actions have the same
cost.

**Source.** Read 2026-09-12 from https://arxiv.org/html/1103.1063v2.
- The monotonicity is Kechris's. Abért–Weiss, *Bernoulli actions are weakly contained in any free
  action*, §1: "A. Kechris showed that for finitely generated groups and free actions, the cost is
  monotonic with respect to weak containment [7, Corollary 10.14], so Theorem 1 leads to the
  following."
- Their Theorem 9 extends it to groupoid cost: "Let f and g be p.m.p. actions of the finitely
  generated group Γ on (X,ℬ,μ) and (Y,𝒞,ν), respectively, such that f weakly contains g. Then
  gcost(f)≤gcost(g)."

Reference [7] of Abért–Weiss was not read here, so the corollary number is as they print it.
`fpbs-bernoulli-noise-does-not-change-cost-proof` cites the monotonicity as Abért–Weiss Theorem 9.
This node imports it as a claim, so routes can require it.
