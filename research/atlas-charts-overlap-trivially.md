---
rg: 2
id: atlas-charts-overlap-trivially
kind: claim
title: The two atlas charts intersect trivially, so the source is unamalgamated and the kernel is free
distinct_from:
  atlas-relator-central-sufficiency: that says which relator lists are usable; this says where the relators can and cannot come from — none arise from chart overlap, since there is none.
  atlas-kernel-window-length-nine: that bounds the length of usable relators from below by a finite-quotient screen; this is an exact structural computation about the chart subgroups themselves.
artifacts:
  - research/artifacts/atlas-relator-extraction-2026-08-15.md
  - experiments/atlas_relator_chart_overlap.py
---

For the canonical atlas source `P̄ = K₁ * K₂ ≅ A₈ * A₈ ↠ Q` with the two
recorded prefix-code charts `D₁ = (01, 1, 000, 001)`,
`D₂ = (00, 1, 010, 011)`:

**Theorem (exact computation).**  The chart algebras
`A_i = span{δ_u δ_v^* : u, v ∈ D_i}` are 16-dimensional with
`dim(A₁ ∩ A₂) = 3`, and the chart subgroups satisfy

```text
K₁ ∩ K₂ = 1   in Q.
```

**Consequences.**

1. `K₁ *_{K₁∩K₂} K₂ = K₁ * K₂`: there is **no amalgam layer**, so the
   standard identify-the-common-subgroup route to a relative presentation
   of `Q` yields nothing, and every relator is a genuine mixed-chart
   Steinberg relation.
2. `R̄` meets every conjugate of each factor trivially, so `R̄` acts
   freely on the Bass–Serre tree of `P̄` and is a **free group** of
   infinite rank — `π₁` of the coset graph on `Q/K₁ ⊔ Q/K₂` with edge
   set `Q`.  Normal generation of subgroups between `N̄` and `R̄` is a
   statement about finitely many `Q`-orbits of cycles; the shortest
   cycles have syllable length 4 and are the twenty radius-2
   cross-chart commutators.
3. A warning for the Steinberg translation
   (`atlas-steinberg-rank-five-translation`): the common refinement
   `{000,001,010,011,1}` of `D₁, D₂` is NOT a usable prefix code for the
   rank-5 chart — refinement must be uniform (the `m(α) = m(β)` rank
   condition of the atlas doc), and it refines `D₁` with multiplicities
   `(1,1,2,1)`; this is the same fact as `K₁ ∩ K₂ = 1`.  The uniform
   refinements have `4·2^k` leaves, so a rank-5 chart must be chosen
   independently of both charts.

Reproduction: `python3 experiments/atlas_relator_chart_overlap.py`
(seconds; exact `F₂`/prefix arithmetic).  Derivation:
`research/artifacts/atlas-relator-extraction-2026-08-15.md` §(c).
