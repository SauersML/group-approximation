---
rg: 2
id: fpbs-relative-stage-costs-bound-cost-by-stage-liminf
kind: claim
title: If relative costs along a finitely generated subgroup chain are at most the positive parts of the stage-cost increments, the total cost is at most the liminf of stage costs
distinct_from:
  fpbs-shifted-stage-relative-cost-zero-or-infinite: that is a 0-or-infinity dichotomy for relative cost over a stage of a shift-invariant action; this is a general upper bound on total cost from bounded stage-to-stage relative costs, with no invariance assumption.
  fpbs-relative-fixed-price-fg-pairs: that is the open inequality for finitely generated pairs; this lemma only assumes it along one chain and derives the cost bound.
artifacts:
  - research/artifacts/fpbs-relative-fixed-price-decomposition-2026-09-17.md
---

**ESTABLISHED** through `fpbs-relative-stage-costs-bound-cost-by-stage-liminf-proof`.

Let `a` be a p.m.p. action of a countable group `Γ`. Let `Γ_1 ≤ Γ_2 ≤ ⋯` be
finitely generated subgroups with union `Γ`. Put `R_n = E_{a|Γ_n}` and
`c_n = C(R_n) < ∞`. Suppose

```text
relC(R_m ; R_n) ≤ (c_m − c_n)^+        for all n < m.
```

Then `C(E_a) ≤ liminf_n c_n`.

If the `c_n` are integers, it is enough to have `relC(R_{n_{k+1}}; R_{n_k}) = 0`
along a subsequence with `c_{n_k} = liminf c_n`.

No fixed price input is used. For subgroup chains, the lemma drops the
hypothesis `C(∪R_n) < ∞` from `C(∪R_n) ≤ liminf C(R_n)` ([TD] Prop 6.7), and
assumes the relative inequality in its place.
