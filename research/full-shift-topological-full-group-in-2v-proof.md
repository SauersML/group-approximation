---
rg: 2
id: full-shift-topological-full-group-in-2v-proof
kind: route
title: Conjugate by the baker's-map coordinates and refine to uniform dyadic grids
target: full-shift-topological-full-group-embeds-in-2v
requires: []
artifacts:
  - research/artifacts/raags-in-2v-via-full-shift-full-group-2026-09-16.md
---

Full proof: Part A of the artifact. Credit: Salo, arXiv:2103.06663v1, Section 2.

Here `C = {0,1}^N`, and `2V` is the group of homeomorphisms of `C^2` that map
the bricks of one dyadic subdivision canonically (by prefix replacement in each
coordinate) onto the bricks of another.

1. **Coordinates.** `Φ(a, b)_i = a_i` and `Φ(a, b)_{-1-i} = b_i` for `i ≥ 0`.
   `Φ` is a homeomorphism `C^2 → X`, so `f ↦ F = Φ^{-1} f Φ` is an injective
   homomorphism `[[X]] → Homeo(C^2)`.
2. **Window.** For `f ∈ [[X]]` the cocycle `c` is continuous, hence locally
   constant with finitely many values. Choose `r ≥ 1` with `|c| ≤ r` and `c(x)`
   depending only on `x_{[-r, r-1]}`. The cylinders `[u.v]` with `|u| = |v| = r`
   correspond to the bricks `vC × u^R C` of the uniform grid `G_r`.
3. **Canonical on grid bricks.** On `[u.v]` with `c ≡ k`, the map
   `σ^k` moves `k` letters across the origin. For `k ≥ 0`, `F` is canonical from
   `vC × u^R C` onto `v_{[k,r)}C × (v_{[0,k)})^R u^R C`. For `k = -m < 0`, `F`
   is canonical onto `u_{[-m,-1]} v C × (u_{[-r,-m)})^R C`. The image brick has
   prefix lengths `(r-k, r+k)`, both in `[0, 2r]`.
4. **Refinement.** Each image brick is a union of cells of `G_{2r}`. Pulling a
   cell `E` back gives the brick `F^{-1}(E)`, and for fixed `Q ∈ G_r` these are
   the uniform subdivision of `Q` by `r+k` halvings in coordinate 1 and `r-k` in
   coordinate 2. So the domain bricks form a dyadic subdivision (first `G_r`,
   then inside each `Q`), `F` is canonical from each onto a cell of `G_{2r}`, and
   the cells of `G_{2r}` form a dyadic subdivision. Hence `F ∈ 2V`. ∎
