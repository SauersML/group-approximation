---
rg: 2
id: fpbs-finite-alphabet-models-suffice-for-fixed-price
kind: claim
title: A finitely generated group has fixed price once every essentially free ergodic invariant measure on a finite-alphabet shift has Bernoulli cost
distinct_from:
  fpbs-factor-invariance-equals-fixed-price: that equates fixed price with cost invariance under free factor maps; this reduces the class of actions that must be tested to free ergodic finite-alphabet shift measures, through a factor of the product with a Bernoulli shift.
  fpbs-free-action-cost-at-least-bernoulli-cost: that is the open lower bound for all free actions; this proves that testing free ergodic finite-alphabet shift measures is enough.
  fpbs-fixed-price-countable-from-finitely-generated: that passes from finitely generated groups to countable groups; this stays inside one finitely generated group and shrinks the class of actions.
artifacts:
  - research/artifacts/fpbs-finite-alphabet-models-suffice-for-fixed-price-proof-attempt-2026-09-17.md
---

**OPEN.** A drafted proof is recorded as an attempt (see Attempts). It is not established because the
referee vote of lens 1 was lost; lenses 2 and 3 returned *survives*.

Let `G` be an infinite finitely generated group and `b` a nontrivial Bernoulli shift of `G`.
The following are equivalent.

1. `G` has fixed price: all essentially free p.m.p. actions of `G` have the same cost.
2. For every finite set `K` and every essentially free ergodic `G`-invariant Borel probability
   measure `nu` on `K^G`, `C(nu) >= C(b)`.

**Scope label.** This is a reduction of the class of test actions, not a partial result
towards fixed price. It is what lets the Seward approximation theorem, which is stated for
ergodic actions of finite Rokhlin entropy, act on every free action.

## Attempts

1. **Ergodic decomposition, product with Bernoulli, finite truncation of a near-optimal graphing and descent
   to the finite-partition factor (2026-09-17).** Formerly the route
   `fpbs-finite-alphabet-models-suffice-for-fixed-price-proof` (requires [fpbs-clopen-certificate-cost-transfer,
   abert-weiss-free-actions-weakly-contain-bernoulli, cost-is-constant-on-weak-equivalence-classes]); see
   `research/artifacts/fpbs-finite-alphabet-models-suffice-for-fixed-price-proof-attempt-2026-09-17.md`.
   Demoted on 2026-09-17 after the referee audit of `fpbs-fixed-price-iff-cost-lsc-at-bernoulli`: the vote of
   lens 1 was lost, so the full referee pass required for ESTABLISHED did not complete. Lenses 2 and 3 returned
   *survives*; lens 3 checked the ergodic-component inequality, the lift of a graphing to `a x b`, the
   truncation, and freeness and ergodicity of the descended factor. No mathematical error has been reported.
   The premise `fpbs-clopen-certificate-cost-transfer` was demoted for the same reason. Restore the route once
   a full referee pass survives.
