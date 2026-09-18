---
rg: 2
id: fpbs-sandwich-cost-fiber-formula-proof
kind: route
title: Restrict sandwiches to one fibre of the finite factor, rescale cost by the induction formula, and bound intermediate ranks by strong inertness
target: fpbs-sandwich-cost-fiber-formula
requires:
  - gaboriau-induction-formula-complete-section
  - gaboriau-treeable-free-action-realizes-min-cost
  - rank-two-free-subgroups-are-strongly-inert
artifacts:
  - research/artifacts/fpbs-sandwich-cost-fiber-formula-2026-09-17.md
---

The full proof is §1–§3 of the artifact. Write `Y = X × Δ/N`,
`A = X × {N}`, `R = E_{b_N}` and `T = E_{b_N|K}`.

1. `R|A = E_{b|N}` and `T|A = E_{b|K∩N}` under `A ≅ X`. This holds because
   `γ(x, N) ∈ A` iff `γ ∈ N`.
2. `KN = Δ` makes `A` a complete section of `T`, and hence of every
   sandwich `E`.
3. `E ↦ E|A` and `E' ↦ E' ∨ T` are mutually inverse bijections of sandwich
   lattices. To see this, merge the `T`-steps of a chain whose `E'`-steps
   have endpoints in `A`: each merged `T`-segment has both endpoints in `A`,
   so it lies in `T|A ⊆ E'`.
4. `gaboriau-induction-formula-complete-section` with `ν(A) = 1/d` gives
   `C(E) − 1 = (C(E|A) − 1)/d`. Taking infima over the bijection gives (A).
   Part (B) follows because `s_Δ × Δ/N` is free and `s_Δ|N ≅ s_N`.
5. For (C), `[K : K∩N] = d`, so `rk(K∩N) = 1 + d` by the Schreier count.
   Also `K ∩ M' = K ∩ N` for `K∩N ≤ M' ≤ N`.
   `rank-two-free-subgroups-are-strongly-inert` makes the trivial double
   coset alone give `d = rr(K∩N) ≤ rr(M')`.
   `gaboriau-treeable-free-action-realizes-min-cost` item 1 gives
   `C(E_{b|M'}) = rk M'` for a free action. Step 4 then gives cost
   `1 + (rk M' − 1)/d ≥ 2`. In `F_2`, any `M ⊇ K` has `rk M ≥ 2`, and
   `C(E_b) = 2`.
