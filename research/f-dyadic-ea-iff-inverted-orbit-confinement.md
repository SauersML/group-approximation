---
rg: 2
id: f-dyadic-ea-iff-inverted-orbit-confinement
kind: claim
title: Extensive amenability of Thompson's F on the dyadic rationals is equivalent to subexponential confinement of the inverted orbit of a random walk on F
distinct_from:
  thompson-f-dyadic-action-is-extensively-amenable: that is the extensive amenability itself, still open; this is a proven equivalent probabilistic reformulation of it, independent of the walk.
  affine-lamplighter-amenable-iff-extensively-amenable: that is the general lamplighter reformulation of extensive amenability; this specializes the inverted-orbit form of the same equivalence to F acting on the dyadic rationals.
artifacts:
  - research/artifacts/hl-f-extensive-amenability-dyadic-2026-09-14.md
---

**ESTABLISHED (citation, equivalence).** Fix a non-degenerate symmetric finitely supported probability
measure `μ` on `F` with generating support, a base point `x_0 ∈ D` (the dyadic rationals in `(0,1)`), and
the left random walk `g_n = h_n⋯h_1` with `h_i` i.i.d. `∼ μ`. Let

`O_n = { x_0, g_1⁻¹x_0, …, g_n⁻¹x_0 } ⊆ D`

be the inverted orbit. The following are equivalent:

1. `F ↷ D` is extensively amenable (`thompson-f-dyadic-action-is-extensively-amenable`);
2. `lim_{n→∞} −(1/n) log E(2^{−|O_n|}) = 0`;
3. for every `ε > 0`, `P(|O_n| < ε n) > e^{−ε n}` for infinitely many `n`;
4. the switch-walk-switch random walk on the lamplighter `(Z/2)^{(D)} ⋊ F` has return probability to the
   trivial configuration decaying subexponentially: `−(1/n) log P(f_n = f_0) → 0`.

By the cited proposition, conditions 2–4 do not depend on the choice of `μ` or `x_0`. So extensive
amenability of `F ↷ D` is the single intrinsic statement that the inverted orbit is confined to `o(n)`
points on events of only subexponentially small probability.

**Why it matters.** With `f-dyadic-action-is-not-recurrent` (mean inverted orbit grows linearly), this
pins the exact analytic target: any proof of extensive amenability of `F ↷ D` — hence of co-amenability of
Jones' subgroup, the Aiello–Brothier–Conti question — must establish condition 3, and cannot go through
recurrence of the dyadic Schreier graph. A subexponential lower bound failing (a genuine exponential
return-probability decay of the dyadic lamplighter) would instead prove `F` nonamenable.

`F ↷ D` is transitive and `F` is finitely generated, so the proposition applies.

Proof route: `f-dyadic-ea-iff-inverted-orbit-confinement-proof`.
