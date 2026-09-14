---
rg: 2
id: orthogonal-popa-corners-kazhdan-small-trace-proof
kind: route
title: Weighted canonical corner vectors in the coarse bimodule turn 2-norm defects on the corner into exact relative almost-invariance bounds, which add up over orthogonal corners
target: orthogonal-popa-corners-for-kazhdan-approximants-small-trace
requires: []
artifacts:
  - research/artifacts/sk-popa-lgx-plan-2026-09-13.md
---

Complete proof (sk-popa-lgx, 2026-09-13). Notation as in the target claim. Steps 1–3 of route `kazhdan-generators-admit-no-norm-popa-corners-proof` are used verbatim:
- (K) `max_{s∈S}‖λ_sζ − ζλ_s‖ ≥ ε‖ζ‖` on `H = L²(M) ⊗ L²(M)`;
- the weighted canonical vector `ζ` of `(p, B)`, with `‖ζ‖² = τ(p)`, `pζ = ζ = ζp` and `bζ = ζb` for `b ∈ B`;
- (A) `‖yζ − ζy‖ ≤ 2(dist(pyp,B) + ‖[y,p]‖)‖ζ‖`.

**Step 1: exact 2-norm transfer.** For `a ∈ M`, `‖aζ‖ = ‖ap‖_2` and `‖ζa‖ = ‖pa‖_2`.
- `aζ = Σ_r c_r Σ_{i,j} (ae^r_{ij})^ ⊗ ê^r_{ji}`. The second tensor factors are pairwise orthogonal, so

  `‖aζ‖² = Σ_r c_r² Σ_{i,j} ‖ae^r_{ij}‖_2² ‖e^r_{ji}‖_2² = Σ_r c_r² Σ_{i,j} τ(a*a e^r_{ii}) τ(e^r_{ii})`.

  This uses `‖ae_{ij}‖_2² = τ(e_{ji}a*ae_{ij}) = τ(a*ae_{ii})` and `‖e_{ji}‖_2² = τ(e_{ii})`.
- With `τ(e^r_{ii}) = τ(p_r)/k_r` and `c_r² = τ(p_r)^{-1}`, the sum over `j` gives `k_r·τ(p_r)/k_r`, so

  `‖aζ‖² = Σ_r Σ_i τ(a*a e^r_{ii}) = τ(a*ap) = ‖ap‖_2²`.

- Symmetrically, the first tensor factors of `ζa = Σ_r c_r Σ_{i,j} ê^r_{ij} ⊗ (e^r_{ji}a)^` are pairwise orthogonal. With `‖e_{ji}a‖_2² = τ(e_{ii}aa*)`, this gives `‖ζa‖² = τ(paa*) = ‖pa‖_2²`.

**Step 2: one corner.** Let `(p, B)` satisfy `‖[y_s,p]‖ ≤ η` and `dist(py_sp,B) ≤ η` for all `s`, with `4η < ε`. By (A) and Step 1,

`‖λ_sζ − ζλ_s‖ ≤ ‖y_sζ − ζy_s‖ + ‖a_sζ‖ + ‖ζa_s‖ ≤ 4η‖ζ‖ + ‖a_sp‖_2 + ‖pa_s‖_2`.

By (K) and `‖ζ‖ = τ(p)^{1/2}`, some `s ∈ S` satisfies `(ε − 4η)τ(p)^{1/2} ≤ ‖a_sp‖_2 + ‖pa_s‖_2`. This is the relative badness statement. Squaring with `(u+v)² ≤ 2u² + 2v²` and bounding the one `s` by the sum over all of `S`:

`(ε − 4η)² τ(p) ≤ 2 Σ_{s∈S} ( ‖a_sp‖_2² + ‖pa_s‖_2² )`.   (C)

**Step 3: orthogonal families.** Apply (C) to each `(p_m, B_m)` and add.
- The `p_m` are orthogonal, so `Σ_m ‖a p_m‖_2² = Σ_m τ(a*a p_m) = τ(a*aP) = ‖aP‖_2²`.
- Likewise `Σ_m ‖p_m a‖_2² = τ(Paa*) = ‖Pa‖_2²`. For countable families both series converge in the trace.
- So `(ε − 4η)² Σ_m τ(p_m) ≤ 2 Σ_s (‖a_sP‖_2² + ‖Pa_s‖_2²)`.
- Finally `‖a_sP‖_2 ≤ ‖a_s‖_2` and `‖Pa_s‖_2 ≤ ‖a_s‖_2`, which gives the second inequality. ∎
