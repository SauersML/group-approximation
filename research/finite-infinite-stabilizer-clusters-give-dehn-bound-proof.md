---
rg: 2
id: finite-infinite-stabilizer-clusters-give-dehn-bound-proof
kind: route
title: "Collapse each finite cluster of infinite-stabilizer cells to a cone vertex and apply Llosa Isenrich–Weis Theorem C"
target: finite-infinite-stabilizer-clusters-give-dehn-bound
requires:
  - llosa-isenrich-weis-dehn-bound-for-cocompact-actions
artifacts:
  - research/artifacts/zp-dehn-finite-cluster-collapse-2026-09-17.md
---

Reduction to Theorem C. The full argument is in
`research/artifacts/zp-dehn-finite-cluster-collapse-2026-09-17.md`.

1. **Components (§1).** For a component `C` of `X_∞` with setwise stabilizer
   `G_C`: `G_x ≤ G_C` for `x ∈ C`, `C / G_C` is finite, `C^(1)` is connected,
   and there are finitely many orbits of components.
2. **Subdivide (§2.1).** Pass to the barycentric subdivision `X'`. Then no
   simplex meets two components of `X'_∞`, and
   `δ_{X'}(n) ≤ 6 δ_X(n) + c_0 n`.
3. **Collapse (§2.2–2.3).** Send each component `C` to a cone vertex `c_C`,
   to get a `G`-complex `Y` with a simplicial `G`-map `f : X' → Y`. Lift loops
   of `Y` by paths of length `≤ D` inside the components. Then `Y` is simply
   connected and `δ_Y(n) ≤ δ_{X'}((D + 1) n)`. Admissible fillings push
   forward, and degenerate 2-cells go to the 1-skeleton.
4. **Stabilizers (§2.4).**
   - `Stab(c_C) = G_C`, and every other simplex has finite stabilizer.
   - Vertex-dimension labels rule out inversions.
   - `[G_C : G_x] < ∞` for a vertex `x ∈ C` of `X`, since `G_C` permutes the
     finite set `C^(0)`. So `G_C` is finitely presented and
     `δ_{G_C} ≃ δ_{G_x}` (Alonso 1990).
5. **Apply Theorem C (§2.4).** Theorem C of
   `llosa-isenrich-weis-dehn-bound-for-cocompact-actions` applies to `Y`,
   whose edge groups are finite, so `[G_e : G_σ] < ∞`. It is read under (N),
   as the root statement is; read literally it is degenerate for free actions.
   Finite edge groups give `edist_Y‾(m) = m`, which yields (A).
6. **(UB) (§3).**
   - For doubling `δ_{G_x}`: `δ(Km) ≤ C δ(m)` and `dist_X‾(m) ≥ m`.
   - In general, replace the generating set `S` of `G` by the ball of radius
     `R = c(K + 2)`. Then `dist_X(m) ≥ K m`, since an infinite vertex group
     satisfies `dist^S_H(m) ≥ m/c − 2`.
7. **Corollary B (§4).** Along an edge of `C`, stabilizers are commensurable.
   So `H ≤ G_C ≤ Comm_G(H)`, every `G_C`-orbit in `C^(0)` is finite, and `C`
   is finite.

Definitions (`≼`, `dist^G_H`, admissible maps, `FVol`, `δ_X`) are those of
Llosa Isenrich–Weis, arXiv:2608.07191v1, §2.1, Definitions 2.2–2.3.
