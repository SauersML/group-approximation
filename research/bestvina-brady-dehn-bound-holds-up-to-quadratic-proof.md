---
rg: 2
id: bestvina-brady-dehn-bound-holds-up-to-quadratic-proof
kind: route
title: Bestvina–Brady groups of degree at most two are bounded by every kernel because every kernel contains Z^2
target: bestvina-brady-dehn-bound-holds-up-to-quadratic
requires:
  - bestvina-brady-dehn-function-classification
---

Let `χ : A_Γ → Z` be surjective with `K_χ` finitely presented. By the
classification, `δ_{BB_Γ} ≃ n^{d(Γ)}` with `d(Γ) ≤ 2`.

- If `d(Γ) = 1`, then `δ_{BB_Γ}` is linear, and every Dehn function
  `≽ n` under the standard equivalence, which absorbs linear terms.
- If `d(Γ) = 2`, then `Γ` is not a tree. `Δ(Γ)` is simply connected, so `Γ`
  is connected, and not being a tree it contains a cycle. If `Δ(Γ)` had no
  2-simplex it would equal the graph `Γ`, which has nontrivial fundamental
  group. So `Γ` contains a triangle `{u, v, w}`, and `A_Γ` contains
  `Z^3 = ⟨u, v, w⟩`. The kernel of `χ` restricted to this `Z^3` has rank at
  least 2, so `K_χ` contains `Z^2`. A group containing `Z^2` is not
  hyperbolic, and a finitely presented group with subquadratic Dehn function
  is hyperbolic (Gromov; Olshanskii, Bowditch, Papasoglu). So
  `δ_{K_χ} ≽ n^2 ≃ δ_{BB_Γ}`.
