---
rg: 2
id: fpbs-bernoulli-cost-usc-on-marked-groups
kind: claim
title: Bernoulli cost is upper but not lower semicontinuous on infinite marked groups, so marked-limit transfers of fixed price die
distinct_from:
  burton-kechris-cost-usc-and-maximum-action: that is upper semicontinuity in the action, for one fixed group, on the space of actions or weak-equivalence classes; this is upper semicontinuity in the group, on the space of marked groups, for the Bernoulli shift.
  fpbs-cost-lsc-at-bernoulli-shift-measures: that asks lower semicontinuity at the uniform Bernoulli measure among shift measures of one group; this proves the group-variable version fails at free groups.
  kk-witness-counterexample-locus-is-marked-closed: that is the marked-group closedness of Kadison--Kaplansky counterexamples; this is the analogous computation for cost, where closedness fails.
  decidable-groups-have-right-computable-l2-betti-numbers: that gives right-computability of L2 Betti numbers; this gives the same for Bernoulli cost and combines the two into a Pi^0_2 form of fixed price.
artifacts:
  - research/artifacts/fpbs-bernoulli-cost-marked-usc-2026-09-20.md
---

**ESTABLISHED.** Let `G_k^∞` be the closed subspace of infinite groups in the space
of `k`-marked groups. Write `C*(Γ) = C(s_Γ)`, the maximal cost of a free action.

1. **Upper semicontinuity.** If `Γ_n → Γ` in `G_k^∞`, then
   `limsup_n C*(Γ_n) ≤ C*(Γ)`. In particular, the groups whose Bernoulli shift has
   cost one form a `G_δ`.
2. **Failure of lower semicontinuity.** Let `Γ_n = ⟨a_1, …, a_k | [a_i, a_1^n]⟩`.
   These groups have fixed price one and converge to `F_k`, while `C*(F_k) = k`. So no
   finite ball of `F_k` certifies `C* > 1` or `β_1^(2) > 0`.
3. **Arithmetic form.** For decidable word problem, `C*` is right-computable. With the
   L2 Betti side, `C* = 1 + β_1^(2)` is a `Π^0_2` statement, and a counterexample has
   no finite witness.

**Consequence (class kill).** Take any approach that proves
`C*(Γ) = 1 + β_1^(2)(Γ)`, which is cycle-tail compactness for `s_Γ`, on approximants
`Γ_n → Γ`, and then passes to the limit through ball-local or semicontinuity data.
Every such approach dies at the upper bound for `C*(Γ)`.
- Both sides are only upper semicontinuous.
- The limit step needs lower semicontinuity of `C*`, and item 2 refutes that at free
  groups.
- With `β_1^(2)` convergence added, the step is equivalent to continuity of `C*`, which
  is the conclusion itself.

Proof: route `fpbs-bernoulli-cost-usc-on-marked-groups-proof`.
