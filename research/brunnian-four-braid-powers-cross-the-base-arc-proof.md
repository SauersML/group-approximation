---
rg: 2
id: brunnian-four-braid-powers-cross-the-base-arc-proof
kind: route
title: "Intersection numbers of arcs grow under powers of a pseudo-Anosov Brunnian 4-braid"
target: brunnian-four-braid-powers-cross-the-base-arc
requires: []
artifacts:
  - research/artifacts/zp-burau-four-strand-mechanism-2026-09-13.md
---

Let `1 ≠ Φ ∈ Brun_4`. By `brunnian-four-braids-are-pseudo-anosov` (established), its image `Φ̄`
in the mapping class group of `S = S_{0,5}` is pseudo-Anosov. Here `S` is obtained from `D_4` by
collapsing the boundary to a fifth marked point `∞`.

1. **From the disk to the sphere.** `β_*^3` becomes an arc `β̄` from `∞` to `p_3`. An isotopy of
   arcs in `D_4` (rel `∂D_4` and the marked points) induces one in `S`, so
   `ι_{D_4}(α, (β_*^3)Φ^k) ≥ ι_S(α, Φ̄^k(β̄))`.
2. **From arcs to curves.** Let `c = ∂N(β̄)` and `d = ∂N(α)` bound narrow regular neighborhoods.
   - `d` separates `{p_1,p_2}` from `{p_3,p_4,∞}`, and `c` separates `{p_3,∞}` from `{p_1,p_2,p_4}`.
     Both are essential in `S`.
   - `α` and `Φ̄^k(β̄)` have disjoint endpoint sets, so near the endpoints the neighborhood
     boundaries do not meet. Each crossing of the arcs gives four crossings of the boundaries.
   - Putting the arcs in minimal position gives
     `i(d, Φ̄^k(c)) ≤ 4 · ι_S(α, Φ̄^k(β̄))`, because `Φ̄^k(c) = ∂N(Φ̄^k(β̄))`.
3. **Growth under a pseudo-Anosov** (Fathi–Laudenbach–Poénaru, *Travaux de Thurston sur les
   surfaces*, exposé 12). Let `λ > 1` be the stretch factor, and `F^s, F^u` the stable and
   unstable measured foliations. For essential simple closed curves `a, b`,
   `i(Φ̄^k(a), b) / λ^k → i(a, F^s) · i(F^u, b)` (up to a normalizing constant). Both factors are
   positive, since the foliations of a pseudo-Anosov are arational and so meet every essential
   curve. So `i(Φ̄^k(c), d) → ∞`.

Combining 1–3: `ι_{D_4}(α, (β_*^3)Φ^k) → ∞`.

The consequence in the claim body is the elementary step `Φ ∈ ker ρ_4 ⇒ Φ^k ∈ ker ρ_4`, together
with `Φ^k ≠ 1` (torsion-freeness) and `Φ^k ∈ Brun_4`. ∎

Imported input: the FLP growth theorem for pseudo-Anosov maps. The exact theorem number in exposé 12
was not re-read here.
