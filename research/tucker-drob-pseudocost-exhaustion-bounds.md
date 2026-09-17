---
rg: 2
id: tucker-drob-pseudocost-exhaustion-bounds
kind: claim
title: Pseudocost is bounded by costs along any exhaustion, equals cost when cost is finite, and is at least the group cost for free actions of finite-cost groups
artifacts:
  - research/artifacts/fpbs-locally-free-fixed-pseudocost-2026-09-17.md
  - research/artifacts/fpbs/docs/fixed-price-countable-passage.md
---

**ESTABLISHED (literature import).** Let `E` be a m.p. countable Borel
equivalence relation on `(X, μ)`.
- **Definition.** An *exhaustion* of `E` is a sequence
  `E_0 ⊆ E_1 ⊆ ⋯` with `⋃ E_n = E`. The pseudocost is
  `PC_μ(E) = inf { liminf_n C_μ(E_n) : (E_n) exhausts E }`. For an action `a`,
  `PC(a) = PC_μ(E_a)`.
- **(1)** If `C_μ(E) < ∞`, then `PC_μ(E) = C_μ(E)`.
- **(2)** If `E` is treeable, then `PC_μ(E) = C_μ(E)`.
- **(3)** `PC_μ(E) = 1` iff `C_μ(E) = 1`.
- **(4)** Let `Γ` be countably infinite with `C(Γ) < ∞`. Then every free
  m.p. action `b` of `Γ` and every exhaustion `(E_n)` of `E_b` satisfy
  `liminf_n C_μ(E_n) ≥ C(Γ)`. Hence `PC(b) ≥ C(Γ)`.

These are Tucker-Drob arXiv:1211.6395, Def 6.6, Cor 6.8 and Prop 6.26(1). They
were already used in the passage artifact (tool table, §1). This node makes
them available to the graph.

Route: `tucker-drob-pseudocost-exhaustion-bounds-citation`.
