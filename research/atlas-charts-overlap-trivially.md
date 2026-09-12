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
3. What the non-uniformity of the join costs — *corrected 2026-08-15,
   late; the first version of this consequence overstated it and would
   have steered the construction away from the code that worked.*  The
   common refinement `E = {000,001,010,011,1}` of `D₁, D₂` IS a legal
   complete prefix code (the join), and it is exactly the code the
   dictionary of `atlas-rank-five-dictionary` runs on, with the shared
   leaf as its hinge.  Because `E` refines `D₁` with multiplicities
   `(1,1,2,1)` — non-uniformly, the same fact as `K₁ ∩ K₂ = 1` — the
   group `GL(E)` contains neither `K₁` nor `K₂`, so no rank-five root
   element is a *chart element*.  That blocks chart-containment only:
   the criterion needs the root elements to be *words* in `K₁ ∪ K₂`,
   which they are.  The `4·2^k`-leaf uniform refinements remain correct
   for their actual role — the superperfect hosts `G_i ⊇ K_i` of §9 —
   not as the Steinberg chart.
4. **No true-kernel packet can kill a chart factor algebraically.**  For
   every subset `T ⊆ R̄`, its normal closure in `P̄` satisfies

   ```text
   <<T>>_(P̄) ⊆ R̄,
   <<T>>_(P̄) ∩ K_i = 1  (i=1,2).
   ```

   Thus adjoining the thirty A4 packet words, collision `19243`, or any
   other finite collection of genuine Leavitt-kernel words can never make
   either `A8` factor collapse in the exact quotient.  Searching for such a
   quotient certificate is logically vacuous.  The atlas route must use a
   normalized-HS statement about regular multiplicities or holonomy; its
   desired obstruction cannot be purely algebraic normal generation inside
   the faithful chart factors.

Reproduction: `python3 experiments/atlas_relator_chart_overlap.py`
(seconds; exact `F₂`/prefix arithmetic).  Derivation:
`research/artifacts/atlas-relator-extraction-2026-08-15.md` §(c).
